############################################
# Copyright (c) 2026 Microsoft Corporation
# Require native smoke receipts for the exact files passed to release publishing.
############################################
import argparse
import json
from pathlib import Path
import shutil

from smoke import read_provenance, verify_jar
from workflow_inputs import context
from mk_java_package import json_bytes, metadata_names, package_basename, sha256, write_checksums

MODES = {'bundled', 'system', 'system-base', 'missing', 'unsupported', 'skip', 'temp-failure'}


def verify(packages, receipts, out, expected):
    provenance = read_provenance(packages)
    if (provenance['prototype'] or provenance.get('workflow') != expected
            or provenance['source_commit'] != expected['source_commit']
            or provenance['release_commit'] != expected['source_commit']):
        raise ValueError('Release validation requires this source/run/attempt, without prototype inputs')
    results = {}
    for path in receipts.rglob('receipt.json'):
        receipt = json.loads(path.read_text(encoding='utf-8'))
        platform = receipt['platform']
        if platform in results or platform not in provenance['platforms']:
            raise ValueError('Duplicate or unexpected smoke platform: ' + platform)
        if (receipt.get('passed') is not True or any(receipt[key] != provenance[key]
                for key in ('source_commit', 'generator_sha256', 'loader_sha256'))
                or set(receipt['artifacts']) != {platform, 'all'}):
            raise ValueError('Invalid source identity or incomplete smoke receipt: ' + platform)
        for classifier, result in receipt['artifacts'].items():
            jar, _ = verify_jar(packages, provenance, classifier)
            if (result.get('passed') is not True or set(result['modes']) != MODES
                    or result['jar_name'] != jar.name or result['jar_sha256'] != sha256(jar.read_bytes())):
                raise ValueError('Smoke receipt does not validate the final JAR: ' + classifier)
        results[platform] = receipt
    if set(results) != set(provenance['platforms']):
        raise ValueError('Missing native smoke results for release platforms')
    sums_name = metadata_names(provenance)[1]
    checksums = {}
    for line in (packages / sums_name).read_text(encoding='ascii').splitlines():
        digest, name = line.split('  ', 1)
        if Path(name).name != name or name in checksums or sha256((packages / name).read_bytes()) != digest:
            raise ValueError('Release checksum mismatch or duplicate entry: ' + name)
        checksums[name] = digest
    if set(checksums) != {p.name for p in packages.iterdir() if p.is_file() and p.name != sums_name}:
        raise ValueError('Release checksum manifest does not cover every output')
    shutil.copytree(packages, out)  # Refuse stale outputs.
    report = {'workflow': expected, 'platforms': results, 'passed': True}
    (out / (package_basename(provenance) + '-java-validation.json')).write_bytes(json_bytes(report))
    write_checksums(out, sums_name)
    print('PASS release gate:', sorted(results), '->', out)


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('--packages', type=Path, required=True)
    parser.add_argument('--receipts', type=Path, required=True)
    parser.add_argument('--out-dir', type=Path, required=True)
    parser.add_argument('--source-commit', required=True)
    parser.add_argument('--repository', required=True)
    parser.add_argument('--run-id', required=True)
    parser.add_argument('--run-attempt', required=True)
    parser.add_argument('--release-version', required=True)
    args = parser.parse_args()
    try:
        verify(args.packages, args.receipts, args.out_dir, context(args))
    except (ValueError, KeyError, OSError) as ex:
        parser.exit(1, 'Java release validation failed: ' + str(ex) + '\n')


if __name__ == '__main__':
    main()
