############################################
# Copyright (c) 2026 Microsoft Corporation
# Prepare fast-test inputs with the current generator and pinned release JNI.
############################################
import argparse
import difflib
import json
from pathlib import Path
import subprocess
import sys
import urllib.request
import zipfile

SCRIPTS = Path(__file__).resolve().parents[1]
ROOT = SCRIPTS.parent
sys.path.insert(0, str(SCRIPTS))
from mk_java_package import (LOADER_CLASS, NATIVE_CLASS, checked_zip, json_bytes,
                             require_entry, sha256, write_jar)


def download(url, digest, target):
    target.parent.mkdir(parents=True, exist_ok=True)
    if target.exists():
        data = target.read_bytes()
    else:
        print('Downloading:', url, flush=True)
        request = urllib.request.Request(url, headers={'User-Agent': 'z3-java-packaging'})
        with urllib.request.urlopen(request, timeout=120) as response:
            data = response.read()
        if sha256(data) != digest:
            raise ValueError('Download checksum mismatch: ' + url)
        target.write_bytes(data)
    if sha256(data) != digest:
        raise ValueError('Cached input checksum mismatch: ' + str(target))
    return data


def run(command):
    result = subprocess.run([str(arg) for arg in command], text=True, encoding='utf-8',
                            errors='replace', capture_output=True)
    if result.returncode:
        raise ValueError('Command failed: ' + str(command[0]) + '\n' + result.stdout + result.stderr)
    return result.stdout


def native_family(entries):
    return sorted(name for name in entries if name == NATIVE_CLASS + '.class'
                  or name.startswith(NATIVE_CLASS + '$') and name.endswith('.class'))


def signatures(classpath, family):
    names = [name[:-6].replace('/', '.') for name in family]
    text = run(['javap', '-classpath', classpath, '-p', '-s', *names])
    return '\n'.join(line for line in text.splitlines() if not line.startswith('Compiled from '))


def prepare(lock_path, work, platforms):
    lock = json.loads(lock_path.read_text(encoding='utf-8'))
    work.mkdir(parents=True, exist_ok=True)
    archives = work / 'downloads'
    for platform in platforms:
        asset = lock['platforms'][platform]
        expected = 'https://github.com/Z3Prover/z3/releases/download/' + lock['tag'] + '/' + asset['name']
        if asset['url'] != expected:
            raise ValueError('Unexpected official release URL')
        download(asset['url'], asset['sha256'], archives / asset['name'])
    first = lock['platforms'][platforms[0]]
    entry = first['name'][:-4] + '/java/com.microsoft.z3.jar'
    # Validate names/duplicates without decompressing debug symbols.
    api_data = require_entry(checked_zip((archives / first['name']).read_bytes(), [entry]), entry)
    api = checked_zip(api_data)
    if LOADER_CLASS in api:
        raise ValueError('Pinned API unexpectedly already contains loader')
    official = work / 'official-api.jar'
    official.write_bytes(api_data)
    source_root = work / 'release-source'
    for path, source in lock['sources'].items():
        url = 'https://raw.githubusercontent.com/Z3Prover/z3/' + lock['commit'] + '/' + path
        download(url, source['sha256'], source_root / path)
    generated = work / 'generated'
    classes = work / 'classes'
    for directory in (generated, classes):
        if directory.exists() and any(directory.iterdir()):
            raise ValueError('Use a fresh work directory for generation: ' + str(directory))
        directory.mkdir(exist_ok=True)
    headers = [source_root / 'src/api' / name for name in lock['headers']]
    run([sys.executable, SCRIPTS / 'update_api.py', *headers,
         '--java-input-dir', source_root / 'src/api/java',
         '--java-output-dir', generated, '--java-package-name', 'com.microsoft.z3'])
    loader = ROOT / 'src/api/java/NativeLibraryLoader.java'
    empty_sourcepath = work / 'empty-sourcepath'
    empty_sourcepath.mkdir(exist_ok=True)
    run(['javac', '--release', '8', '-implicit:none', '-sourcepath', empty_sourcepath,
         '-classpath', official, '-d', classes, generated / 'Native.java', loader])
    replacements = {p.relative_to(classes).as_posix(): p.read_bytes() for p in classes.rglob('*.class')}
    family = native_family(api)
    if family != native_family(replacements):
        raise ValueError('Generated Native nested-class set differs from official API')
    if set(replacements) != set(family) | {LOADER_CLASS}:
        raise ValueError('Unexpected extra classes compiled while preparing API')
    before, after = signatures(official, family), signatures(classes, family)
    if before != after:
        diff = '\n'.join(difflib.unified_diff(before.splitlines(), after.splitlines(),
                                             fromfile='release Native ABI', tofile='current generator ABI'))
        raise ValueError('Native JVM member signature mismatch:\n' + diff[:8000])
    patched = {**api, **replacements}
    patched_api = work / 'prepared-api.jar'
    write_jar(patched_api, patched)
    # Assert every unrelated API entry is unchanged, including all other API classes.
    actual = checked_zip(patched_api.read_bytes())
    for name, data in api.items():
        if name not in replacements and actual.get(name) != data:
            raise ValueError('Unrelated API entry changed: ' + name)
    provenance = {
        'release_commit': lock['commit'], 'release_version': lock['version'],
        'release_runtime_version': lock['runtime_version'],
        'source_commit': run(['git', '-C', ROOT, 'rev-parse', 'HEAD']).strip(),
        'generator_sha256': sha256((SCRIPTS / 'update_api.py').read_bytes()),
        'loader_sha256': sha256(loader.read_bytes()),
        'generated_native_sha256': sha256((generated / 'Native.java').read_bytes()),
        'compiler': run(['javac', '-version']).strip(), 'java_release': 8,
        'original_api_sha256': sha256(api_data), 'api_sha256': sha256(patched_api.read_bytes()),
        'native_signature_sha256': sha256(before.encode('utf-8')),
        'native_class_count': len(family), 'non_native_entries_unchanged': True,
    }
    (work / 'preparation.json').write_bytes(json_bytes(provenance))
    print('Prepared current-branch loader; checked', len(family), 'Native classes and unchanged API entries.')
    return provenance


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--release-lock', type=Path, default=Path(__file__).with_name('release.json'))
    parser.add_argument('--work-dir', type=Path, required=True)
    parser.add_argument('--platform', action='append', required=True)
    args = parser.parse_args()
    try:
        prepare(args.release_lock, args.work_dir, args.platform)
    except (ValueError, OSError, KeyError, zipfile.BadZipFile) as ex:
        parser.exit(1, 'Java preparation failed: ' + str(ex) + '\n')


if __name__ == '__main__':
    main()
