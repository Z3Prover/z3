############################################
# Copyright (c) 2026 Microsoft Corporation
# Record and collect current-source artifacts from one GitHub Actions run.
############################################
import argparse
import json
from pathlib import Path
import re
import shutil
import subprocess
import sys

SCRIPTS = Path(__file__).resolve().parents[1]
ROOT = SCRIPTS.parent
sys.path.insert(0, str(SCRIPTS))
from mk_java_package import checked_zip, json_bytes, require_entry, sha256


def source_version():
    runtime = (SCRIPTS / 'VERSION.txt').read_text(encoding='ascii').strip()
    if not re.fullmatch(r'\d+\.\d+\.\d+\.\d+', runtime):
        raise ValueError('Unexpected scripts/VERSION.txt format')
    return runtime.rsplit('.', 1)[0], runtime


def context(args):
    actual = subprocess.check_output(['git', '-C', ROOT, 'rev-parse', 'HEAD'], text=True).strip()
    if actual != args.source_commit:
        raise ValueError('Checkout does not match expected source commit')
    if args.release_version and source_version()[0] != args.release_version:
        raise ValueError('Release workflow version does not match scripts/VERSION.txt')
    return {'repository': args.repository, 'run_id': args.run_id,
            'run_attempt': args.run_attempt, 'source_commit': actual}


def record(zip_root, out, classifier, expected):
    version, runtime = source_version()
    zips = list(zip_root.rglob('*.zip'))
    if len(zips) != 1 or not zips[0].name.startswith('z3-' + version + '-'):
        raise ValueError('Expected one version-matched native distribution ZIP under ' + str(zip_root))
    archive = zips[0]
    receipt = {'classifier': classifier, 'workflow': expected, 'version': version,
               'runtime_version': runtime, 'name': archive.name, 'sha256': sha256(archive.read_bytes())}
    out.mkdir(parents=True, exist_ok=True)
    (out / ('receipt-' + classifier + '.json')).write_bytes(json_bytes(receipt))
    print('Recorded native artifact:', classifier, archive.name, expected)


def validate_receipt(receipt, expected, version, runtime, classifier):
    if (receipt['workflow'] != expected or receipt['classifier'] != classifier
            or receipt['version'] != version or receipt['runtime_version'] != runtime):
        raise ValueError('Mixed run, attempt, source, version or platform in native artifact receipt')
    name = receipt['name']
    if Path(name).name != name or not name.startswith('z3-' + version + '-') or not name.endswith('.zip'):
        raise ValueError('Unexpected native archive name')


def collect(downloads, out, platforms, expected):
    version, runtime = source_version()
    if out.exists():
        raise ValueError('Use a fresh collection output directory')
    selected = {}
    names = set()
    for classifier in platforms:
        directory = downloads / ('java-native-' + classifier)
        receipts = list(directory.rglob('receipt-*.json'))
        archives = list(directory.rglob('*.zip'))
        if len(receipts) != 1 or len(archives) != 1:
            raise ValueError('Expected exactly one receipt and ZIP for ' + classifier)
        receipt = json.loads(receipts[0].read_text(encoding='utf-8'))
        validate_receipt(receipt, expected, version, runtime, classifier)
        archive = archives[0]
        if (archive.name != receipt['name'] or archive.name in names
                or sha256(archive.read_bytes()) != receipt['sha256']):
            raise ValueError('Duplicate or checksum/name-mismatched native ZIP: ' + archive.name)
        names.add(archive.name)
        selected[classifier] = (receipt, archive)
    if len(selected) != len(platforms) or not selected:
        raise ValueError('Select nonduplicate platforms')
    out.mkdir(parents=True)
    assets = {}
    for classifier, (receipt, archive) in selected.items():
        shutil.copyfile(archive, out / archive.name)
        assets[classifier] = {'name': receipt['name'], 'sha256': receipt['sha256'],
                             'workflow': expected,
                             'url': 'https://github.com/' + expected['repository'] + '/actions/runs/' + expected['run_id']}
    # API classes already come from this source build, including Native and loader.
    first = next(iter(selected.values()))[1]
    entry = first.name[:-4] + '/java/com.microsoft.z3.jar'
    api = require_entry(checked_zip(first.read_bytes(), [entry]), entry)
    (out / 'prepared-api.jar').write_bytes(api)
    provenance = {
        'input_kind': 'workflow-artifact', 'workflow': expected,
        'source_commit': expected['source_commit'], 'release_commit': expected['source_commit'],
        'release_version': version, 'release_runtime_version': runtime,
        'generator_sha256': sha256((SCRIPTS / 'update_api.py').read_bytes()),
        'loader_sha256': sha256((ROOT / 'src/api/java/NativeLibraryLoader.java').read_bytes()),
        'api_sha256': sha256(api), 'java_release': 8,
    }
    lock = {'input_kind': 'workflow-artifact', 'version': version, 'runtime_version': runtime,
            'commit': expected['source_commit'], 'platforms': assets}
    (out / 'inputs.json').write_bytes(json_bytes(lock))
    (out / 'preparation.json').write_bytes(json_bytes(provenance))
    print('Collected native artifacts from one source/run/attempt:', expected)


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('mode', choices=['record', 'collect'])
    parser.add_argument('--source-commit', required=True)
    parser.add_argument('--repository', required=True)
    parser.add_argument('--run-id', required=True)
    parser.add_argument('--run-attempt', required=True)
    parser.add_argument('--release-version', help='Require the release workflow and source versions to agree')
    parser.add_argument('--platform', action='append', required=True)
    parser.add_argument('--input-dir', type=Path, required=True)
    parser.add_argument('--out-dir', type=Path, required=True)
    args = parser.parse_args()
    try:
        expected = context(args)
        if args.mode == 'record':
            if len(args.platform) != 1:
                raise ValueError('Record one platform at a time')
            record(args.input_dir, args.out_dir, args.platform[0], expected)
        else:
            collect(args.input_dir, args.out_dir, args.platform, expected)
    except (ValueError, KeyError, OSError) as ex:
        parser.exit(1, 'Java workflow inputs failed: ' + str(ex) + '\n')


if __name__ == '__main__':
    main()
