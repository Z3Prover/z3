############################################
# Copyright (c) 2026 Microsoft Corporation
# Assemble and validate an unpublished, local Maven repository rehearsal.
############################################
import argparse
import hashlib
import json
from pathlib import Path
import re
from xml.etree import ElementTree as ET
import zipfile

from maven_artifacts import NS
import maven_auto
from smoke import verify_jar
from verify_release import MODES
from mk_java_package import checked_zip, json_bytes, sha256, write_checksums, write_jar


def read_family(packages):
    report = json.loads((packages / 'maven-preparation.json').read_bytes())
    identity = report['maven']
    if report['prototype'] is not True or identity['groupId'] != 'invalid.z3.prototype':
        raise ValueError('Repository rehearsal accepts only unpublished test coordinates')
    for key in ('artifactId', 'version'):
        if not re.fullmatch(r'[A-Za-z0-9_][A-Za-z0-9_.-]*', identity[key]) or '..' in identity[key]:
            raise ValueError('Unsafe Maven coordinate: ' + key)
    provenance = report['input_provenance']
    if not isinstance(provenance['prototype'], bool) or not re.fullmatch(r'[0-9a-f]{40}', report['source_commit']):
        raise ValueError('Invalid source identity or input provenance mode')
    if (report['source_commit'] != provenance['source_commit']
            or report['api_source_commit'] != provenance['release_commit']
            or report['platforms'] != provenance['platforms']
            or report['runtime_version'] != provenance['release_runtime_version']
            or identity['artifactId'] != provenance['distribution']['artifactId']
            or identity['version'] != provenance['distribution']['version']):
        raise ValueError('Maven family differs from its input provenance')
    platforms = report['platforms']
    if not platforms or len(set(platforms)) != len(platforms):
        raise ValueError('Missing or duplicate platforms')
    if any(not re.fullmatch(r'(linux|win|osx)-(x64|arm64)', p) for p in platforms):
        raise ValueError('Unsafe or unknown platform classifier')
    base = identity['artifactId'] + '-' + identity['version']
    expected = {}
    for variant in ['', *platforms, 'all']:
        for kind in ('', 'sources', 'javadoc'):
            key = '-'.join(p for p in (variant, kind) if p)
            expected[key] = base + ('-' + key if key else '') + '.jar'
    if report['artifacts'] != expected or set(report['jar_sha256']) != set(expected.values()):
        raise ValueError('Incomplete or unexpected Maven artifact family')
    names = {*expected.values(), base + '.pom', 'maven-preparation.json'}
    checksums = {}
    for line in (packages / 'SHA256SUMS').read_text(encoding='ascii').splitlines():
        digest, name = line.split('  ', 1)
        if name not in names or name in checksums:
            raise ValueError('Unexpected or duplicate Maven checksum entry: ' + name)
        checksums[name] = digest
    if (set(checksums) != names or {p.name for p in packages.iterdir()} != names | {'SHA256SUMS'}
            or any(p.is_symlink() or not p.is_file() for p in packages.iterdir())):
        raise ValueError('Maven checksum manifest must cover the exact artifact family')
    for name, digest in checksums.items():
        if sha256((packages / name).read_bytes()) != digest:
            raise ValueError('Maven checksum mismatch: ' + name)
    root = ET.fromstring((packages / (base + '.pom')).read_bytes())
    def text(path):
        node = root.find('/'.join('{' + NS + '}' + part for part in path.split('/')))
        return '' if node is None or node.text is None else node.text.strip()
    for path, value in {**identity, 'scm/tag': report['source_commit'], 'packaging': 'jar'}.items():
        if text(path) != value:
            raise ValueError('POM identity differs from preparation: ' + path)
    for path in ('name', 'description', 'url', 'licenses/license/name', 'licenses/license/url',
                 'developers/developer/name', 'scm/connection', 'scm/developerConnection', 'scm/url'):
        if not text(path):
            raise ValueError('Missing POM metadata: ' + path)
    if root.find('{' + NS + '}distributionManagement') is not None:
        raise ValueError('Rehearsal POM must not configure remote deployment')
    if any(root.find('{' + NS + '}' + name) is not None for name in ('dependencies', 'profiles')):
        raise ValueError('Runtime POM must not add automatic platform dependencies')
    entries = {}
    for key, name in expected.items():
        data = (packages / name).read_bytes()
        if sha256(data) != report['jar_sha256'][name]:
            raise ValueError('Prepared JAR hash mismatch: ' + name)
        entries[key] = checked_zip(data)
    validation = report['source_validation']
    if validation['api_sha256'] != report['jar_sha256'][expected['']]:
        raise ValueError('Source validation used a different API JAR')
    source_files = {name: sha256(data) for name, data in entries['sources'].items() if name.endswith('.java')}
    if not source_files or source_files != validation['files']:
        raise ValueError('Source companion differs from validated sources')
    for path in ('index.html', 'com/microsoft/z3/Context.html', 'com/microsoft/z3/Version.html',
                 'com/microsoft/z3/enumerations/Z3_lbool.html'):
        if path not in entries['javadoc']:
            raise ValueError('Missing Javadoc page: ' + path)
    for variant in [*platforms, 'all']:
        verify_jar(packages, provenance, variant)
        for kind in ('sources', 'javadoc'):
            if report['jar_sha256'][expected[variant + '-' + kind]] != report['jar_sha256'][expected[kind]]:
                raise ValueError('Classifier companion differs from shared API companion')
    return report


def repository_files(packages, report):
    identity = report['maven']
    prefix = '/'.join([*identity['groupId'].split('.'), identity['artifactId'], identity['version']])
    names = [*report['artifacts'].values(), identity['artifactId'] + '-' + identity['version'] + '.pom']
    files = {prefix + '/' + name: (packages / name).read_bytes() for name in sorted(names)}
    selector = maven_auto.identity(report)
    selector_prefix = '/'.join([*selector['groupId'].split('.'), selector['artifactId'], selector['version']])
    files[selector_prefix + '/' + selector['artifactId'] + '-' + selector['version'] + '.pom'] = maven_auto.pom(report)
    for path, data in list(files.items()):
        # MD5/SHA-1 are repository compatibility files, not our integrity gate.
        for algorithm in ('md5', 'sha1', 'sha256', 'sha512'):
            digest = hashlib.new(algorithm, data, usedforsecurity=False).hexdigest()
            files[path + '.' + algorithm] = (digest + '\n').encode('ascii')
    return files


def repository_digest(files):
    return sha256(json_bytes({name: sha256(data) for name, data in sorted(files.items())}))


def prepare_repository(packages, out):
    report = read_family(packages)
    files = repository_files(packages, report)
    out.mkdir(parents=True, exist_ok=False)
    for name, data in files.items():
        path = out / name
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_bytes(data)
    print('PASS local Maven repository:', len(files), 'files;', repository_digest(files))


def check_repository(repository, packages, report):
    files = repository_files(packages, report)
    paths = list(repository.rglob('*'))
    if (not repository.is_dir() or repository.is_symlink() or any(p.is_symlink() for p in paths)
            or {p.relative_to(repository).as_posix() for p in paths if p.is_file()} != set(files)):
        raise ValueError('Repository contains missing or unexpected files')
    for name, data in files.items():
        if (repository / name).read_bytes() != data:
            raise ValueError('Repository bytes differ from prepared artifacts: ' + name)
    return repository_digest(files)


def check_receipts(packages, report, repository_sha, consumers, smokes):
    preparation_sha = sha256((packages / 'maven-preparation.json').read_bytes())
    consumer_results, smoke_results = {}, {}
    for path in sorted(consumers.rglob('receipt.json')):
        receipt = json.loads(path.read_bytes())
        platform = receipt['platform']
        required = {tool + ':' + kind for tool in ('maven', 'gradle') for kind in (platform, 'all')}
        required.add('maven:auto')
        if (platform not in report['platforms'] or platform in consumer_results
                or receipt['source_commit'] != report['source_commit']
                or receipt['preparation_sha256'] != preparation_sha
                or receipt.get('repository_sha256') != repository_sha
                or set(receipt['results']) != required):
            raise ValueError('Missing, duplicate or stale Maven/Gradle consumer receipt')
        for key, result in receipt['results'].items():
            variant = platform if key == 'maven:auto' else key.split(':')[1]
            name = report['artifacts'][variant]
            if key == 'maven:auto' and (result.get('selected_platform') != platform
                    or result.get('selector_sha256') != sha256(maven_auto.pom(report))
                    or result.get('unsupported_rejected') is not True):
                raise ValueError('Automatic selector did not validate the current platform and POM')
            if (result.get('passed') is not True or result.get('sources_javadoc_resolved') is not True
                    or result['sha256'] != report['jar_sha256'][name]):
                raise ValueError('Consumer did not validate the exact prepared artifacts')
        consumer_results[platform] = receipt
    provenance = report['input_provenance']
    for path in sorted(smokes.rglob('receipt.json')):
        receipt = json.loads(path.read_bytes())
        platform = receipt['platform']
        if (platform not in report['platforms'] or receipt.get('passed') is not True
                or any(receipt[key] != provenance[key] for key in
                       ('source_commit', 'generator_sha256', 'loader_sha256'))
                or set(receipt['artifacts']) != {platform, 'all'}):
            raise ValueError('Invalid native smoke receipt')
        for key, result in receipt['artifacts'].items():
            name = report['artifacts'][key]
            if (result.get('passed') is not True or set(result['modes']) != MODES
                    or result['jar_name'] != name or result['jar_sha256'] != report['jar_sha256'][name]):
                raise ValueError('Native smoke did not validate the exact prepared JAR')
        # Fast CI tests several Java versions on each platform; validate them all.
        smoke_results.setdefault(platform, []).append(receipt)
    if set(consumer_results) != set(report['platforms']) or set(smoke_results) != set(report['platforms']):
        raise ValueError('Missing platform consumer or native smoke results')
    return {'consumers': consumer_results, 'smokes': smoke_results}


def bundle(packages, repository, consumers, smokes, out, expected):
    report = read_family(packages)
    provenance = report['input_provenance']
    if report['source_commit'] != expected['source_commit']:
        raise ValueError('Bundle source commit differs from the current checkout')
    if not provenance['prototype'] and (provenance.get('workflow') != expected
            or provenance['release_commit'] != expected['source_commit']
            or provenance.get('input_kind') != 'workflow-artifact'):
        raise ValueError('Bundle requires native inputs from this source/run/attempt')
    digest = check_repository(repository, packages, report)
    receipts = check_receipts(packages, report, digest, consumers, smokes)
    out.mkdir(parents=True, exist_ok=False)
    target = out / 'maven-rehearsal.zip'
    write_jar(target, repository_files(packages, report))
    manifest = {'publishable': False, 'signed': False, 'maven': report['maven'], 'workflow': expected,
                'repository_sha256': digest, 'bundle_sha256': sha256(target.read_bytes()),
                'preparation_sha256': sha256((packages / 'maven-preparation.json').read_bytes()),
                'preparation': report, 'validation': receipts}
    (out / 'rehearsal.json').write_bytes(json_bytes(manifest))
    write_checksums(out, 'SHA256SUMS')
    print('PASS unpublished Maven bundle:', sorted(report['platforms']), '->', target)


def main():
    parser = argparse.ArgumentParser()
    commands = parser.add_subparsers(dest='command', required=True)
    prepare = commands.add_parser('prepare')
    validate = commands.add_parser('verify')
    for command in (prepare, validate):
        command.add_argument('--packages', type=Path, required=True)
        command.add_argument('--out-dir', type=Path, required=True)
    for name in ('repository', 'consumer-receipts', 'smoke-receipts'):
        validate.add_argument('--' + name, type=Path, required=True)
    for name in ('source-commit', 'workflow-repository', 'run-id', 'run-attempt'):
        validate.add_argument('--' + name, required=True)
    args = parser.parse_args()
    try:
        if args.command == 'prepare':
            prepare_repository(args.packages, args.out_dir)
        else:
            expected = {'source_commit': args.source_commit, 'repository': args.workflow_repository,
                        'run_id': args.run_id, 'run_attempt': args.run_attempt}
            bundle(args.packages, args.repository, args.consumer_receipts, args.smoke_receipts,
                   args.out_dir, expected)
    except (OSError, KeyError, ValueError, ET.ParseError, zipfile.BadZipFile) as error:
        parser.exit(1, 'Maven repository rehearsal failed: ' + str(error) + '\n')


if __name__ == '__main__':
    main()
