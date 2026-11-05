############################################
# Copyright (c) 2026 Microsoft Corporation
# Stage existing, tested Java artifacts with standard Maven publishing plugins.
############################################
import argparse
import hashlib
import io
import json
import os
from pathlib import Path
import re
import shutil
import urllib.error
import urllib.request
import zipfile
from xml.etree import ElementTree as ET

from maven_artifacts import TEST_GROUP, validate_group
from maven_bundle import check_receipt_data, read_family, repository_digest, repository_files
from prepare import run
from mk_java_package import checked_zip, json_bytes, sha256, write_jar

CENTRAL_PLUGIN = 'org.sonatype.central:central-publishing-maven-plugin:0.12.0:publish'
DEPLOY_PLUGIN = 'org.apache.maven.plugins:maven-deploy-plugin:3.2.0:deploy-file'
SIGN_PLUGIN = 'org.apache.maven.plugins:maven-gpg-plugin:3.2.8:sign-and-deploy-file'


def preflight(mode, group, artifact, environ):
    if mode == 'disabled':
        return 'SKIP Maven Central: publication is disabled; no credentials required.'
    if mode not in ('validate', 'publish'):
        raise ValueError('Unknown publication mode')
    validate_group(group)
    if group.startswith(('invalid.', 'example.', 'test.')) or not artifact:
        raise ValueError('Maintainer-approved Maven groupId/artifactId must be configured')
    if environ.get('GITHUB_REPOSITORY') != 'Z3Prover/z3' or environ.get('GITHUB_EVENT_NAME') != 'workflow_dispatch':
        raise ValueError('Central deployment is restricted to an upstream release workflow dispatch')
    required = ('CENTRAL_USERNAME', 'CENTRAL_PASSWORD', 'MAVEN_GPG_KEY', 'MAVEN_GPG_PASSPHRASE')
    missing = [name for name in required if not environ.get(name)]
    if missing:
        raise ValueError('Publication requested but configuration is missing: ' + ', '.join(missing))
    return 'Maven Central configuration present: ' + mode


def verified_inputs(packages, rehearsal, group, expected, production=False):
    report = read_family(packages, group)
    manifest = json.loads((rehearsal / 'rehearsal.json').read_bytes())
    data = (rehearsal / 'maven-rehearsal.zip').read_bytes()
    files = repository_files(packages, report)
    digest = repository_digest(files)
    if (manifest['workflow'] != expected or manifest['preparation'] != report
            or manifest['maven'] != report['maven'] or report['source_commit'] != expected['source_commit']
            or manifest['preparation_sha256'] != sha256((packages / 'maven-preparation.json').read_bytes())
            or manifest['repository_sha256'] != digest or manifest['bundle_sha256'] != sha256(data)
            or checked_zip(data) != files):
        raise ValueError('Publication inputs differ from the exact verified Maven bundle')
    provenance = report['input_provenance']
    if production and (provenance['prototype'] or provenance.get('input_kind') != 'workflow-artifact'
            or provenance.get('workflow') != expected or report['api_source_commit'] != expected['source_commit']
            or not re.fullmatch(r'\d+\.\d+\.\d+', report['maven']['version'])):
        raise ValueError('Central deployment requires a stable, current-source, same-run/attempt build')
    # Reapply the existing receipt gate, including the selected Maven POM and
    # runtime hashes, rather than trusting a boolean in a downloaded report.
    check_receipt_data(packages, report, digest,
        list(manifest['validation']['consumers'].values()),
        [receipt for values in manifest['validation']['smokes'].values() for receipt in values])
    return report


def deployed_path(repository, name, version):
    path = repository / name
    if not version.endswith('-SNAPSHOT'):
        return path
    # Local deploy-file rehearsals use Maven's timestamped snapshot filenames.
    # Stable production deployment rejects SNAPSHOT versions before staging.
    artifact = path.parent.parent.name
    suffix = path.name[len(artifact + '-' + version):]
    extension = path.suffix[1:]
    classifier = suffix[:-(len(extension) + 1)].removeprefix('-')
    metadata = ET.parse(path.parent / 'maven-metadata.xml').getroot()
    matches = [item.findtext('value') for item in metadata.findall('versioning/snapshotVersions/snapshotVersion')
               if item.findtext('extension') == extension and (item.findtext('classifier') or '') == classifier]
    if len(matches) != 1 or not matches[0] or '/' in matches[0] or '\\' in matches[0]:
        raise ValueError('Missing or ambiguous staged snapshot identity')
    return path.parent / (artifact + '-' + matches[0] + suffix)


def stage(packages, out, group, mvn, signed=False):
    packages, out = packages.resolve(), out.resolve()
    report = read_family(packages, group)
    out.mkdir(parents=True, exist_ok=False)
    repository = out / 'local-deploy'
    bootstrap = out / 'bootstrap.xml'
    bootstrap.write_text('<project><modelVersion>4.0.0</modelVersion><groupId>invalid.z3.publisher</groupId>'
                         '<artifactId>bootstrap</artifactId><version>1</version><packaging>pom</packaging></project>', encoding='utf-8')
    maven = [mvn, '-B', '-ntp', '-f', bootstrap]
    goal = SIGN_PLUGIN if signed else DEPLOY_PLUGIN
    arguments = ['-Durl=' + repository.as_uri(), '-DrepositoryId=local-publication-staging']
    if signed:
        arguments += ['-Dgpg.signer=bc', '-Dgpg.bestPractices=true']
    identity = report['maven']
    base = identity['artifactId'] + '-' + identity['version']
    attachments = {k: v for k, v in report['artifacts'].items() if k}
    run([*maven, goal, *arguments, '-Dfile=' + str(packages / (base + '.jar')),
         '-DpomFile=' + str(packages / (base + '.pom')),
         '-Dfiles=' + ','.join(str(packages / value) for value in attachments.values()),
         '-Dclassifiers=' + ','.join(attachments), '-Dtypes=' + ','.join('jar' for _ in attachments)])
    expected = {name: value for name, value in repository_files(packages, report).items()
                if name.endswith(('.jar', '.pom'))}
    # A selector is POM-only; deploy its validated metadata as a second GAV.
    for name, value in expected.items():
        if name.endswith('.pom') and Path(name).name != base + '.pom':
            source = out / Path(name).name
            source.write_bytes(value)
            run([*maven, goal, *arguments, '-Dfile=' + str(source), '-DpomFile=' + str(source), '-Dpackaging=pom'])
            # Run Central's project-aware goal against the exact tested POM-only
            # selector. No wrapper POM or unbuilt runtime artifact is required.
            (out / 'selector.pom').write_bytes(value)
    staging = out / 'central-staging'
    for name, value in expected.items():
        actual = deployed_path(repository, name, identity['version'])
        if actual.read_bytes() != value:
            raise ValueError('Maven staging changed a tested artifact: ' + name)
        target = staging / name
        target.parent.mkdir(parents=True, exist_ok=True)
        target.write_bytes(value)
        if signed:
            signature = Path(str(actual) + '.asc').read_bytes()
            if not signature.startswith(b'-----BEGIN PGP SIGNATURE-----'):
                raise ValueError('Missing armored signature: ' + name)
            Path(str(target) + '.asc').write_bytes(signature)
    # Explicit inventory avoids deploying local repository metadata or wrapper POMs.
    for path in list(staging.rglob('*')):
        if path.is_file():
            for algorithm in ('md5', 'sha1', 'sha256', 'sha512'):
                digest = hashlib.new(algorithm, path.read_bytes(), usedforsecurity=False).hexdigest()
                Path(str(path) + '.' + algorithm).write_text(digest + '\n', encoding='ascii')
    (out / 'inputs.json').write_bytes(json_bytes({'maven': identity,
        'source_commit': report['source_commit'], 'platforms': report['platforms'],
        'signed': signed, 'workflow': report['input_provenance'].get('workflow')}))
    return report


def central(out, mvn, mode):
    out = out.resolve()
    expected = {p.relative_to(out / 'central-staging').as_posix(): p.read_bytes()
                for p in (out / 'central-staging').rglob('*') if p.is_file()}
    if not expected:
        raise ValueError('Refusing an empty Central staging directory')
    inputs = json.loads((out / 'inputs.json').read_bytes())
    bundle = out / 'target/central-publishing/central-bundle.zip'
    output = ''
    snapshot = inputs['maven']['version'].endswith('-SNAPSHOT')
    if snapshot:
        if mode != 'disabled':
            raise ValueError('Snapshot rehearsals cannot enter Central release deployment')
        # Central's plugin routes snapshots to a separate repository. Fast CI
        # keeps its pinned snapshot identity and checks the local layout only;
        # source-built stable Full Flow exercises the actual Central plugin.
        bundle.parent.mkdir(parents=True, exist_ok=True)
        write_jar(bundle, expected)
    else:
        if mode != 'disabled' and os.name == 'nt':
            raise ValueError('Use the Linux publication workflow; Central plugin ZIP paths differ on Windows')
        # The plugin consumes its staging directory. Keep the validated input
        # inventory intact for a separate rehearsal followed by deployment.
        staging = out / ('plugin-staging-' + mode)
        shutil.copytree(out / 'central-staging', staging)
        output = run([mvn, '-B', '-ntp', '-f', out / 'selector.pom', CENTRAL_PLUGIN,
            '-DpublishingServerId=central', '-DstagingDirectory=' + str(staging),
            '-DoutputDirectory=' + str(bundle.parent),
            '-DskipUpload=' + str(mode == 'disabled').lower(),
            '-DautoPublish=' + str(mode == 'publish').lower(),
            '-DwaitUntil=' + ('published' if mode == 'publish' else 'validated')])
        (out / ('central-' + mode + '.log')).write_text(output, encoding='utf-8')
    data = bundle.read_bytes()
    # Sonatype's plugin emits native separators on Windows. During a local
    # rehearsal, accept only separator variants of the exact known inventory;
    # uploads run on Linux. Never extract or accept unknown/duplicate entries.
    with zipfile.ZipFile(io.BytesIO(data)) as archive:
        entries = archive.infolist()
        names = [item.orig_filename.replace('\\', '/') for item in entries]
        if len(names) != len(set(names)) or set(names) != set(expected):
            raise ValueError('Central plugin bundle has unexpected or duplicate entries')
        actual = {name: archive.read(item) for name, item in zip(names, entries)}
    if set(actual) != set(expected) or any(
            (actual[name].strip() != value.strip() if name.endswith(('.md5', '.sha1', '.sha256', '.sha512'))
             else actual[name] != value) for name, value in expected.items()):
        raise ValueError('Central plugin bundle differs from the staged inventory')
    deployment = re.search(r'deploymentId[:= ]+([0-9a-f-]{36})', output, re.IGNORECASE)
    if mode != 'disabled' and not deployment:
        raise ValueError('Central plugin returned without a deployment ID; publication is unconfirmed')
    (out / 'publication.json').write_bytes(json_bytes({'mode': mode, 'uploaded': mode != 'disabled',
        'auto_publish': mode == 'publish', 'bundle_sha256': sha256(data),
        'bundle_tool': 'python-snapshot-rehearsal' if snapshot else CENTRAL_PLUGIN,
        'state': {'disabled': 'bundle-only', 'validate': 'validated', 'publish': 'published'}[mode],
        'deployment_id': deployment.group(1) if deployment else None,
        'inputs': inputs,
        'files': {name: sha256(value) for name, value in actual.items()}}))


def require_unpublished(packages, report):
    for name in repository_files(packages, report):
        if not name.endswith('.pom'):
            continue
        request = urllib.request.Request('https://repo.maven.apache.org/maven2/' + name,
            method='HEAD', headers={'User-Agent': 'z3-java-publication'})
        try:
            with urllib.request.urlopen(request, timeout=30):
                raise ValueError('Stable Maven coordinates already published; refusing overwrite: ' + name)
        except urllib.error.HTTPError as error:
            if error.code != 404:
                raise ValueError('Cannot determine Central publication state: HTTP ' + str(error.code)) from None


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('command', choices=['preflight', 'stage', 'deploy'])
    parser.add_argument('--mode', choices=['disabled', 'validate', 'publish'], default='disabled')
    parser.add_argument('--group-id', default=TEST_GROUP)
    parser.add_argument('--artifact-id', default='')
    parser.add_argument('--packages', type=Path)
    parser.add_argument('--rehearsal', type=Path)
    parser.add_argument('--out-dir', type=Path)
    parser.add_argument('--mvn', default=shutil.which('mvn') or shutil.which('mvn.cmd'))
    args = parser.parse_args()
    try:
        if args.command == 'preflight':
            print(preflight(args.mode, args.group_id, args.artifact_id, os.environ))
            return
        if args.command == 'deploy' and args.mode == 'disabled':
            print(preflight(args.mode, args.group_id, args.artifact_id, os.environ))
            return
        if not args.mvn or not args.packages or not args.rehearsal or not args.out_dir:
            raise ValueError('Maven, packages, rehearsal and a fresh output directory are required')
        if args.command == 'stage' and args.mode != 'disabled':
            raise ValueError('The stage command never uploads; use deploy for an explicitly enabled publication')
        production = args.command == 'deploy'
        if production:
            print(preflight(args.mode, args.group_id, args.artifact_id, os.environ))
        expected = {key: os.environ[name] for key, name in (
            ('repository', 'GITHUB_REPOSITORY'), ('source_commit', 'GITHUB_SHA'),
            ('run_id', 'GITHUB_RUN_ID'), ('run_attempt', 'GITHUB_RUN_ATTEMPT'))}
        report = verified_inputs(args.packages, args.rehearsal, args.group_id, expected, production)
        if production:
            identity = report['maven']
            if identity['artifactId'] != args.artifact_id:
                raise ValueError('Approved artifactId differs from the tested family')
            if os.environ.get('GITHUB_REF') != 'refs/tags/z3-' + identity['version']:
                raise ValueError('Central deployment must run from the matching immutable release tag')
            require_unpublished(args.packages, report)
        stage(args.packages, args.out_dir, args.group_id, args.mvn, signed=production)
        central(args.out_dir, args.mvn, 'disabled')
        if production:
            central(args.out_dir, args.mvn, args.mode)
    except (OSError, ValueError, KeyError, ET.ParseError) as error:
        parser.exit(1, 'Maven publication failed: ' + str(error) + '\n')


if __name__ == '__main__':
    main()
