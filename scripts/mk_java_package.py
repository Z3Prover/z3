############################################
# Copyright (c) 2026 Microsoft Corporation
# Assemble classifier JARs without compiling native code or rewriting binaries.
############################################
import argparse
import hashlib
import io
import json
from pathlib import Path, PurePosixPath
import re
import struct
import zipfile
from xml.sax.saxutils import escape

RESOURCE_PREFIX = 'com/microsoft/z3/native/'
NATIVE_CLASS = 'com/microsoft/z3/Native'
LOADER_CLASS = 'com/microsoft/z3/NativeLibraryLoader.class'
LIBRARIES = {
    'linux': ('libz3.so', 'libz3java.so'),
    'osx': ('libz3.dylib', 'libz3java.dylib'),
    'win': ('libz3.dll', 'z3java.dll'),
}


def sha256(data):
    return hashlib.sha256(data).hexdigest()


def json_bytes(value):
    return (json.dumps(value, sort_keys=True, indent=2) + '\n').encode('utf-8')


def checked_zip(data, wanted=None):
    """Reject ambiguous and unsafe names even though we never extractall()."""
    result = {}
    with zipfile.ZipFile(io.BytesIO(data)) as archive:
        for item in archive.infolist():
            name = item.filename
            parts = PurePosixPath(name).parts
            if (item.orig_filename != name or name in result or '\\' in name or name.startswith('/')
                    or PurePosixPath(name).as_posix() != name.rstrip('/')
                    or '..' in parts or any(':' in p for p in parts)):
                raise ValueError('Duplicate or unsafe ZIP entry: ' + name)
            result[name] = None
        for item in archive.infolist():
            if not item.is_dir() and (wanted is None or item.filename in wanted):
                result[item.filename] = archive.read(item)
    return {name: data for name, data in result.items() if data is not None}


def require_entry(entries, name):
    try:
        return entries[name]
    except KeyError:
        raise ValueError('Missing required archive entry: ' + name) from None


def validate_binary(data, classifier):
    """Inspect CPU/format headers only; this does not prove dynamic linkability."""
    os_name, arch = classifier.split('-')
    try:
        if os_name == 'win' and data[:2] == b'MZ':
            offset = struct.unpack_from('<I', data, 60)[0]
            if data[offset:offset + 4] != b'PE\0\0':
                raise ValueError('Invalid PE signature')
            machine = struct.unpack_from('<H', data, offset + 4)[0]
            valid = machine == {'x86': 0x14c, 'x64': 0x8664, 'arm64': 0xaa64}[arch]
        elif os_name == 'linux' and data[:4] == b'\x7fELF':
            valid = (data[4:6] == b'\x02\x01' and
                     struct.unpack_from('<H', data, 18)[0] == {'x64': 62, 'arm64': 183}[arch])
        elif os_name == 'osx' and data[:4] == b'\xcf\xfa\xed\xfe':
            valid = struct.unpack_from('<I', data, 4)[0] == {'x64': 0x1000007, 'arm64': 0x100000c}[arch]
        else:
            valid = False
    except (KeyError, IndexError, struct.error) as ex:
        raise ValueError('Malformed binary for ' + classifier) from ex
    if not valid:
        raise ValueError('Binary format/architecture mismatch for ' + classifier)


def write_jar(path, entries):
    with zipfile.ZipFile(path, 'w', zipfile.ZIP_DEFLATED, compresslevel=9) as out:
        names = sorted(entries, key=lambda name: (name != 'META-INF/MANIFEST.MF', name))
        for name in names:
            item = zipfile.ZipInfo(name, (1980, 1, 1, 0, 0, 0))
            item.create_system = 3
            item.external_attr = 0o100644 << 16
            item.compress_type = zipfile.ZIP_DEFLATED
            out.writestr(item, entries[name])


def validate_api(entries):
    for name in (NATIVE_CLASS + '.class', 'com/microsoft/z3/Context.class', LOADER_CLASS):
        data = require_entry(entries, name)
        if data[:4] != b'\xca\xfe\xba\xbe' or len(data) < 8:
            raise ValueError('Invalid Java class: ' + name)
    for name, data in entries.items():
        if name.startswith(RESOURCE_PREFIX) or name == 'META-INF/z3/provenance.json':
            raise ValueError('API JAR already contains native packaging resources: ' + name)
        if re.search(r'^META-INF/.*\.(SF|RSA|DSA|EC)$', name, re.I):
            raise ValueError('Cannot modify signed API JAR: ' + name)
        if name.endswith('.class') and (len(data) < 8 or struct.unpack_from('>H', data, 6)[0] > 52):
            raise ValueError('Class requires newer than Java 8: ' + name)


def assemble(lock, artifacts_dir, api_jar, preparation, out_dir, platforms,
             group_id, artifact_id, version):
    if not platforms or len(set(platforms)) != len(platforms):
        raise ValueError('Select at least one platform, without duplicates')
    for value in (group_id, artifact_id, version):
        if not re.fullmatch(r'[A-Za-z0-9][A-Za-z0-9_.-]*', value):
            raise ValueError('Invalid Maven coordinate: ' + value)
    if not version.startswith(lock['version'] + '-'):
        raise ValueError('Prototype version must derive from release version with a test suffix')
    if (preparation['release_commit'] != lock['commit'] or
            preparation['release_version'] != lock['version'] or
            preparation['api_sha256'] != sha256(api_jar)):
        raise ValueError('Prepared API does not match release/provenance')
    api = checked_zip(api_jar)
    validate_api(api)
    packages = {}
    provenance = {**preparation, 'prototype': True, 'maven': {
        'groupId': group_id, 'artifactId': artifact_id, 'version': version}}
    # Validate every selected input before creating outputs.
    for classifier in platforms:
        asset = lock['platforms'][classifier]
        name = asset['name']
        if lock.get('input_kind') == 'workflow-artifact':
            context = preparation['workflow']
            if (asset.get('workflow') != context or context['source_commit'] != lock['commit']):
                raise ValueError('Mixed workflow run/attempt/source commit: ' + name)
            expected_url = 'https://github.com/' + context['repository'] + '/actions/runs/' + context['run_id']
        else:
            expected_url = 'https://github.com/Z3Prover/z3/releases/download/' + lock['tag'] + '/' + name
        if asset['url'] != expected_url:
            raise ValueError('Unexpected release asset URL: ' + asset['url'])
        if not name.startswith('z3-' + lock['version'] + '-'):
            raise ValueError('Release version mismatch: ' + name)
        data = (Path(artifacts_dir) / name).read_bytes()
        if sha256(data) != asset['sha256']:
            raise ValueError('Release ZIP checksum mismatch: ' + name)
        root = name[:-4]
        wanted = [root + '/java/com.microsoft.z3.jar', root + '/LICENSE.txt']
        wanted += [root + '/bin/' + library for library in LIBRARIES[classifier.split('-')[0]]]
        entries = checked_zip(data, wanted)
        release_api = require_entry(entries, root + '/java/com.microsoft.z3.jar')
        checked_zip(release_api)
        license_text = require_entry(entries, root + '/LICENSE.txt')
        libraries = {}
        for library in LIBRARIES[classifier.split('-')[0]]:
            binary = require_entry(entries, root + '/bin/' + library)
            validate_binary(binary, classifier)
            libraries[library] = binary
        package_provenance = {**provenance, 'classifier': classifier, 'release_asset': asset,
                              'platform_api_sha256': sha256(release_api),
                              'libraries': {k: sha256(v) for k, v in libraries.items()}}
        content = {**api, 'META-INF/z3/LICENSE.txt': license_text,
                   'META-INF/z3/provenance.json': json_bytes(package_provenance)}
        content.update({RESOURCE_PREFIX + classifier + '/' + k: v for k, v in libraries.items()})
        packages[classifier] = content
    out_dir = Path(out_dir)
    if out_dir.exists() and any(out_dir.iterdir()):
        raise ValueError('Output directory must be empty to exclude stale artifacts: ' + str(out_dir))
    out_dir.mkdir(parents=True, exist_ok=True)
    base = artifact_id + '-' + version
    write_jar(out_dir / (base + '.jar'), {**api, 'META-INF/z3/LICENSE.txt': license_text,
                                       'META-INF/z3/provenance.json': json_bytes(provenance)})
    for classifier, content in packages.items():
        write_jar(out_dir / (base + '-' + classifier + '.jar'), content)
    # These explicit test coordinates are not an assertion of an official namespace.
    pom = '''<project xmlns="http://maven.apache.org/POM/4.0.0">
  <modelVersion>4.0.0</modelVersion>
  <groupId>{}</groupId><artifactId>{}</artifactId><version>{}</version>
  <name>Z3 Java packaging prototype</name>
  <description>Unpublished test artifacts; Maven namespace and release ownership are undecided.</description>
  <url>https://github.com/Z3Prover/z3</url>
  <licenses><license><name>MIT License</name><url>https://github.com/Z3Prover/z3/blob/master/LICENSE.txt</url></license></licenses>
</project>
'''.format(escape(group_id), escape(artifact_id), escape(version))
    (out_dir / (base + '.pom')).write_text(pom, encoding='utf-8', newline='\n')
    (out_dir / 'provenance.json').write_bytes(json_bytes({**provenance, 'platforms': platforms}))
    sums = ''.join(sha256(p.read_bytes()) + '  ' + p.name + '\n'
                   for p in sorted(out_dir.iterdir()) if p.is_file())
    (out_dir / 'SHA256SUMS').write_text(sums, encoding='ascii', newline='\n')
    return out_dir


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--release-lock', type=Path, required=True)
    parser.add_argument('--artifacts-dir', type=Path, required=True)
    parser.add_argument('--api-jar', type=Path, required=True)
    parser.add_argument('--preparation', type=Path, required=True)
    parser.add_argument('--out-dir', type=Path, required=True)
    parser.add_argument('--platform', action='append', required=True)
    parser.add_argument('--group-id', required=True)
    parser.add_argument('--artifact-id', required=True)
    parser.add_argument('--version', required=True)
    args = parser.parse_args()
    try:
        out = assemble(json.loads(args.release_lock.read_text(encoding='utf-8')),
                       args.artifacts_dir, args.api_jar.read_bytes(),
                       json.loads(args.preparation.read_text(encoding='utf-8')),
                       args.out_dir, args.platform, args.group_id, args.artifact_id, args.version)
    except (ValueError, KeyError, OSError, zipfile.BadZipFile) as ex:
        parser.exit(1, 'Java packaging failed: ' + str(ex) + '\n')
    print('Java packaging complete:', out)


if __name__ == '__main__':
    main()
