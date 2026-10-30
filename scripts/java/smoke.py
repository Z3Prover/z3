############################################
# Copyright (c) 2026 Microsoft Corporation
# Exercise the exact CI artifacts in fresh JVMs, with no native search-path setup.
############################################
import argparse
import json
import os
from pathlib import Path
import subprocess
import sys

SCRIPTS = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(SCRIPTS))
from mk_java_package import (LIBRARIES, RESOURCE_PREFIX, checked_zip, metadata_names,
                             package_basename, sha256)


def read_provenance(packages):
    candidates = list(packages.glob('*-java-provenance.json'))
    if (packages / 'provenance.json').exists():
        candidates.append(packages / 'provenance.json')
    if len(candidates) != 1:
        raise ValueError('Expected exactly one package provenance manifest')
    provenance = json.loads(candidates[0].read_text(encoding='utf-8'))
    if candidates[0].name != metadata_names(provenance)[0]:
        raise ValueError('Unexpected package provenance filename')
    return provenance


def verify_jar(packages, provenance, classifier):
    base = package_basename(provenance)
    jar = packages / (base + '-' + classifier + '.jar')
    entries = checked_zip(jar.read_bytes())
    embedded = json.loads(entries['META-INF/z3/provenance.json'])
    if (embedded['classifier'] != classifier or any(
            embedded.get(key) != provenance.get(key) for key in (
                'distribution', 'maven', 'prototype', 'workflow', 'source_commit', 'generator_sha256',
                'loader_sha256', 'api_sha256', 'release_commit', 'release_version', 'release_tag',
                'release_runtime_version'))):
        raise ValueError('Artifact provenance mismatch')
    if classifier == 'all':
        platforms = embedded['platforms']
        if set(platforms) != set(provenance['platforms']):
            raise ValueError('Universal platform manifest mismatch')
    else:
        if classifier not in provenance['platforms']:
            raise ValueError('Platform not declared in package manifest')
        platforms = {classifier: embedded}
    expected_resources = set()
    for platform, metadata in platforms.items():
        libraries = LIBRARIES[platform.split('-')[0]]
        if (metadata['classifier'] != platform or metadata['api_sha256'] != provenance['api_sha256']
                or set(metadata['libraries']) != set(libraries)):
            raise ValueError('Platform library manifest mismatch: ' + platform)
        for name in libraries:
            resource = RESOURCE_PREFIX + platform + '/' + name
            expected_resources.add(resource)
            if resource not in entries or sha256(entries[resource]) != metadata['libraries'][name]:
                raise ValueError('Embedded binary checksum mismatch: ' + resource)
    if {name for name in entries if name.startswith(RESOURCE_PREFIX)} != expected_resources:
        raise ValueError('Unexpected native resource set')
    base_entries = checked_zip((packages / (base + '.jar')).read_bytes())
    if ({k: v for k, v in entries.items() if k.endswith('.class')} !=
            {k: v for k, v in base_entries.items() if k.endswith('.class')}):
        raise ValueError('API classes differ between packaging forms')
    return jar, entries


def smoke(packages, platform, work, jar_kind='both'):
    packages = packages.resolve()
    provenance = read_provenance(packages)
    for line in (packages / metadata_names(provenance)[1]).read_text(encoding='ascii').splitlines():
        digest, name = line.split('  ', 1)
        if Path(name).name != name or sha256((packages / name).read_bytes()) != digest:
            raise ValueError('Artifact checksum mismatch: ' + name)
    if platform not in provenance['platforms']:
        raise ValueError('Runner platform not included in package manifest: ' + platform)
    base = package_basename(provenance)
    version = provenance['release_runtime_version']
    base_jar = packages / (base + '.jar')
    classifiers = [platform, 'all'] if jar_kind == 'both' else [platform if jar_kind == 'platform' else 'all']
    artifacts = {classifier: verify_jar(packages, provenance, classifier) for classifier in classifiers}
    work.mkdir(parents=True, exist_ok=False)
    classes = work / 'classes'
    classes.mkdir()

    def run(args, env=None):
        result = subprocess.run([str(a) for a in args], text=True, encoding='utf-8',
                                errors='replace', capture_output=True, env=env)
        if result.returncode:
            raise ValueError('Smoke command failed:\n' + result.stdout + result.stderr)
        return result.stdout + result.stderr

    run(['javac', '-source', '8', '-target', '8', '-cp', base_jar, '-d', classes,
         SCRIPTS / 'java/Smoke.java', SCRIPTS / 'java/LoaderPlatformTest.java'])
    environment = dict(os.environ)
    for name in ('LD_LIBRARY_PATH', 'DYLD_LIBRARY_PATH', 'DYLD_FALLBACK_LIBRARY_PATH',
                 'JDK_JAVA_OPTIONS', '_JAVA_OPTIONS', 'CLASSPATH'):
        environment.pop(name, None)
    receipts = {}
    for classifier, (jar, entries) in artifacts.items():
        variant = work / classifier
        variant.mkdir()
        empty = variant / 'empty-library-path'
        empty.mkdir()
        libraries = LIBRARIES[platform.split('-')[0]]
        results = []
        for mode in ('bundled', 'system', 'system-base', 'missing', 'unsupported', 'skip', 'temp-failure'):
            temp = variant / (mode + '-tmp')
            temp.mkdir()
            native_dir = empty
            artifact = base_jar if mode in ('system-base', 'missing') else jar
            mode_environment = dict(environment)
            if mode in ('system', 'system-base'):
                native_dir = variant / (mode + '-libraries')
                native_dir.mkdir()
                for name in libraries:
                    (native_dir / name).write_bytes(entries[RESOURCE_PREFIX + platform + '/' + name])
                # Native dependencies also need the conventional OS search path.
                if os.name == 'nt':
                    mode_environment['PATH'] = str(native_dir.resolve()) + os.pathsep + mode_environment['PATH']
                else:
                    mode_environment['LD_LIBRARY_PATH'] = str(native_dir.resolve())
                    mode_environment['DYLD_LIBRARY_PATH'] = str(native_dir.resolve())
            if mode == 'temp-failure':
                temp = variant / 'tmp-is-a-file'
                temp.write_text('not a directory', encoding='ascii')
            command = ['java', '-Djava.library.path=' + str(native_dir.resolve()),
                       '-Djava.io.tmpdir=' + str(temp.resolve()), '-cp',
                       str(artifact) + os.pathsep + str(classes.resolve()), 'Smoke', mode, version,
                       ','.join(libraries)]
            print(classifier + ': ' + run(command, mode_environment).strip(), flush=True)
            if mode in ('system', 'system-base', 'missing', 'unsupported', 'skip') and any(temp.iterdir()):
                raise ValueError('Unexpected extraction in mode: ' + mode)
            results.append(mode)
        print(run(['java', '-cp', str(jar) + os.pathsep + str(classes.resolve()),
                   'com.microsoft.z3.LoaderPlatformTest'], environment).strip())
        receipts[classifier] = {'jar_name': jar.name, 'jar_sha256': sha256(jar.read_bytes()),
                               'modes': results, 'passed': True}
    receipt = {'platform': platform, 'artifacts': receipts,
               'java': run(['java', '-XshowSettings:properties', '-version']).strip(),
               'source_commit': provenance['source_commit'],
               'generator_sha256': provenance['generator_sha256'],
               'loader_sha256': provenance['loader_sha256'], 'passed': True}
    (work / 'receipt.json').write_text(json.dumps(receipt, indent=2) + '\n', encoding='utf-8')
    print('PASS exact-artifact smoke:', platform, {k: v['jar_sha256'] for k, v in receipts.items()})


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('--packages', type=Path, required=True)
    parser.add_argument('--platform', required=True)
    parser.add_argument('--work-dir', type=Path, required=True)
    parser.add_argument('--jar-kind', choices=['platform', 'all', 'both'], default='both')
    args = parser.parse_args()
    try:
        smoke(args.packages, args.platform, args.work_dir, args.jar_kind)
    except (ValueError, OSError, KeyError) as ex:
        parser.exit(1, 'Java smoke failed: ' + str(ex) + '\n')


if __name__ == '__main__':
    main()
