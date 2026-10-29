############################################
# Copyright (c) 2026 Microsoft Corporation
# Exercise the exact CI artifact in fresh JVMs, with no native search-path setup.
############################################
import argparse
import json
import os
from pathlib import Path
import subprocess
import sys

SCRIPTS = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(SCRIPTS))
from mk_java_package import LIBRARIES, RESOURCE_PREFIX, checked_zip, sha256


def smoke(packages, platform, work):
    packages = packages.resolve()
    for line in (packages / 'SHA256SUMS').read_text(encoding='ascii').splitlines():
        digest, name = line.split('  ', 1)
        if Path(name).name != name or sha256((packages / name).read_bytes()) != digest:
            raise ValueError('Artifact checksum mismatch: ' + name)
    provenance = json.loads((packages / 'provenance.json').read_text(encoding='utf-8'))
    base = provenance['maven']['artifactId'] + '-' + provenance['maven']['version']
    version = provenance['release_runtime_version']
    jar = packages / (base + '-' + platform + '.jar')
    base_jar = packages / (base + '.jar')
    entries = checked_zip(jar.read_bytes())
    embedded = json.loads(entries['META-INF/z3/provenance.json'])
    if embedded['classifier'] != platform or embedded['api_sha256'] != provenance['api_sha256']:
        raise ValueError('Artifact provenance mismatch')
    expected_resources = {RESOURCE_PREFIX + platform + '/' + name for name in LIBRARIES[platform.split('-')[0]]}
    if {name for name in entries if name.startswith(RESOURCE_PREFIX)} != expected_resources:
        raise ValueError('Unexpected native resource set')
    for resource in expected_resources:
        if sha256(entries[resource]) != embedded['libraries'][resource.rsplit('/', 1)[1]]:
            raise ValueError('Embedded binary checksum mismatch: ' + resource)
    work.mkdir(parents=True, exist_ok=False)
    classes = work / 'classes'
    classes.mkdir()
    # Compile with the runner JDK, including Java 8, using only Java 8 language features.
    def run(args, env=None):
        result = subprocess.run([str(a) for a in args], text=True, encoding='utf-8',
                                errors='replace', capture_output=True, env=env)
        if result.returncode:
            raise ValueError('Smoke command failed:\n' + result.stdout + result.stderr)
        return result.stdout + result.stderr
    run(['javac', '-source', '8', '-target', '8', '-cp', jar, '-d', classes,
         SCRIPTS / 'java/Smoke.java', SCRIPTS / 'java/LoaderPlatformTest.java'])
    empty = work / 'empty-library-path'
    empty.mkdir()
    environment = dict(os.environ)
    for name in ('LD_LIBRARY_PATH', 'DYLD_LIBRARY_PATH', 'DYLD_FALLBACK_LIBRARY_PATH',
                 'JDK_JAVA_OPTIONS', '_JAVA_OPTIONS', 'CLASSPATH'):
        # Do not inherit options that could skip loading or pre-load an installed Z3.
        environment.pop(name, None)
    # The caller's UTF-8 defaults are left intact; Java output is ASCII here.
    results = []
    for mode in ('bundled', 'system', 'missing', 'unsupported', 'skip', 'temp-failure'):
        temp = work / (mode + '-tmp')
        temp.mkdir()
        native_dir = empty
        artifact = jar
        if mode in ('system', 'missing', 'unsupported', 'skip'):
            artifact = base_jar
        if mode == 'system':
            native_dir = work / 'system-libraries'
            native_dir.mkdir()
            for resource in expected_resources:
                (native_dir / resource.rsplit('/', 1)[1]).write_bytes(entries[resource])
        if mode == 'temp-failure':
            temp = work / 'tmp-is-a-file'
            temp.write_text('not a directory', encoding='ascii')
        command = ['java', '-Djava.library.path=' + str(native_dir.resolve()),
                   '-Djava.io.tmpdir=' + str(temp.resolve()), '-cp',
                   str(artifact) + os.pathsep + str(classes.resolve()), 'Smoke', mode, version]
        mode_environment = dict(environment)
        if mode == 'system':
            # A conventional external installation must also expose libz3 to
            # the OS dynamic loader, independently of Java's JNI search path.
            if os.name == 'nt':
                mode_environment['PATH'] = str(native_dir.resolve()) + os.pathsep + mode_environment['PATH']
            else:
                mode_environment['LD_LIBRARY_PATH'] = str(native_dir.resolve())
                mode_environment['DYLD_LIBRARY_PATH'] = str(native_dir.resolve())
        print(run(command, mode_environment).strip(), flush=True)
        if mode == 'system' and any(temp.iterdir()):
            raise ValueError('System loading unexpectedly used extraction fallback')
        results.append(mode)
    print(run(['java', '-cp', str(jar) + os.pathsep + str(classes.resolve()),
               'com.microsoft.z3.LoaderPlatformTest'], environment).strip())
    receipt = {'platform': platform, 'jar_sha256': sha256(jar.read_bytes()),
               'java': run(['java', '-XshowSettings:properties', '-version']).strip(),
               'modes': results, 'source_commit': provenance['source_commit'],
               'generator_sha256': provenance['generator_sha256'],
               'loader_sha256': provenance['loader_sha256'], 'passed': True}
    (work / 'receipt.json').write_text(json.dumps(receipt, indent=2) + '\n', encoding='utf-8')
    print('PASS exact-artifact smoke:', platform, receipt['jar_sha256'])


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('--packages', type=Path, required=True)
    parser.add_argument('--platform', required=True)
    parser.add_argument('--work-dir', type=Path, required=True)
    args = parser.parse_args()
    try:
        smoke(args.packages, args.platform, args.work_dir)
    except (ValueError, OSError, KeyError) as ex:
        parser.exit(1, 'Java smoke failed: ' + str(ex) + '\n')


if __name__ == '__main__':
    main()
