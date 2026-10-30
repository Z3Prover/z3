############################################
# Copyright (c) 2026 Microsoft Corporation
# Prepare unpublished Maven companions using existing Maven plugins.
############################################
import argparse
import json
from pathlib import Path
import shutil
from xml.etree import ElementTree as ET
from xml.sax.saxutils import escape

from prepare import run
from sources import SCRIPTS, verify
from smoke import read_provenance, verify_jar
from mk_java_package import checked_zip, json_bytes, metadata_names, package_basename, sha256, write_checksums

NS = 'http://maven.apache.org/POM/4.0.0'
ET.register_namespace('', NS)


def pom_text(identity, commit):
    text = (SCRIPTS / 'java/maven/pom.xml').read_text(encoding='utf-8')
    for key, value in {**identity, 'commit': commit}.items():
        text = text.replace('@' + {'groupId': 'GROUP', 'artifactId': 'ARTIFACT',
                                  'version': 'VERSION', 'commit': 'COMMIT'}[key] + '@', escape(value))
    return text


def prepare(packages, sources, out, work, mvn):
    packages, sources, out, work = [p.resolve() for p in (packages, sources, out, work)]
    if out.exists() or work.exists():
        raise ValueError('Use fresh Maven output and work directories')
    provenance = read_provenance(packages)
    base = package_basename(provenance)
    # A fixed, deliberately invalid namespace prevents this preparation flow from
    # being mistaken for an approved upstream Maven publication configuration.
    identity = {'groupId': 'invalid.z3.prototype', **provenance['distribution']}
    for line in (packages / metadata_names(provenance)[1]).read_text(encoding='ascii').splitlines():
        digest, name = line.split('  ', 1)
        if Path(name).name != name or sha256((packages / name).read_bytes()) != digest:
            raise ValueError('Maven input checksum mismatch: ' + name)
    variants = ['', *sorted(provenance['platforms']), 'all']
    for classifier in variants[1:]:
        verify_jar(packages, provenance, classifier)
    work.mkdir(parents=True)
    validation = verify(sources, packages / (base + '.jar'), work / 'source-check')
    # Use an isolated source tree so the Maven plugins cannot pick up cache or
    # generated native files. Package the license beside the actual Java sources.
    project = work / 'project'
    project.mkdir()
    source_dir = project / 'src/main/java'
    for name in validation['files']:
        target = source_dir / name
        target.parent.mkdir(parents=True, exist_ok=True)
        shutil.copyfile(sources / name, target)
    license_text = checked_zip((packages / (base + '.jar')).read_bytes())['META-INF/z3/LICENSE.txt']
    (source_dir / 'LICENSE.txt').write_bytes(license_text)
    text = pom_text(identity, provenance['source_commit'])
    root = ET.fromstring(text)
    def child(parent, name, text=None):
        node = ET.SubElement(parent, '{' + NS + '}' + name)
        node.text = text
        return node
    properties = child(root, 'properties')
    child(properties, 'project.build.sourceEncoding', 'UTF-8')
    child(properties, 'project.build.outputTimestamp', '2026-01-01T00:00:00Z')
    build = child(root, 'build')
    child(build, 'finalName', base)
    plugins = child(build, 'plugins')
    for artifact, version in [('maven-source-plugin', '3.4.0'), ('maven-javadoc-plugin', '3.12.0')]:
        plugin = child(plugins, 'plugin')
        child(plugin, 'groupId', 'org.apache.maven.plugins')
        child(plugin, 'artifactId', artifact)
        child(plugin, 'version', version)
        if artifact == 'maven-javadoc-plugin':
            configuration = child(plugin, 'configuration')
            child(configuration, 'source', '8')
            child(configuration, 'doclint', 'none')
            child(configuration, 'notimestamp', 'true')
            child(configuration, 'failOnError', 'true')
            child(configuration, 'detectLinks', 'false')
            child(configuration, 'offline', 'true')
    ET.ElementTree(root).write(project / 'pom.xml', encoding='utf-8', xml_declaration=True)
    run([mvn, '-B', '-ntp', '-f', project / 'pom.xml',
         'org.apache.maven.plugins:maven-source-plugin:3.4.0:jar-no-fork',
         'org.apache.maven.plugins:maven-javadoc-plugin:3.12.0:jar'])
    source_jar = project / 'target' / (base + '-sources.jar')
    doc_jar = project / 'target' / (base + '-javadoc.jar')
    source_entries = checked_zip(source_jar.read_bytes())
    if {k: sha256(v) for k, v in source_entries.items() if k.endswith('.java')} != validation['files']:
        raise ValueError('Maven source plugin changed or omitted Java sources')
    docs = checked_zip(doc_jar.read_bytes())
    for name in ('index.html', 'com/microsoft/z3/Context.html', 'com/microsoft/z3/Version.html',
                 'com/microsoft/z3/enumerations/Z3_lbool.html'):
        if name not in docs:
            raise ValueError('Missing generated Javadoc page: ' + name)
    out.mkdir(parents=True)
    files = {}
    for classifier in variants:
        suffix = '-' + classifier if classifier else ''
        name = base + suffix + '.jar'
        shutil.copyfile(packages / name, out / name)
        files[classifier] = name
        for kind, jar in [('sources', source_jar), ('javadoc', doc_jar)]:
            attachment = classifier + '-' + kind if classifier else kind
            name = base + '-' + attachment + '.jar'
            shutil.copyfile(jar, out / name)
            files[attachment] = name
    (out / (base + '.pom')).write_text(text, encoding='utf-8', newline='\n')
    report = {'prototype': True, 'maven': identity, 'source_commit': provenance['source_commit'],
              'api_source_commit': provenance['release_commit'],
              'input_provenance': provenance,
              'runtime_version': provenance['release_runtime_version'], 'platforms': provenance['platforms'],
              'source_validation': validation, 'artifacts': files,
              'jar_sha256': {name: sha256((out / name).read_bytes()) for name in files.values()},
              'compiler': run(['javac', '-version']).strip()}
    (out / 'maven-preparation.json').write_bytes(json_bytes(report))
    write_checksums(out, 'SHA256SUMS')
    print('Prepared unpublished Maven family:', identity, 'classes:', validation['class_count'])


def main():
    parser = argparse.ArgumentParser()
    for name in ('packages', 'sources', 'out-dir', 'work-dir'):
        parser.add_argument('--' + name, type=Path, required=True)
    parser.add_argument('--mvn', default=shutil.which('mvn') or shutil.which('mvn.cmd'))
    args = parser.parse_args()
    try:
        if not args.mvn:
            raise ValueError('Maven is required for source/Javadoc plugins')
        prepare(args.packages, args.sources, args.out_dir, args.work_dir, args.mvn)
    except (ValueError, KeyError, OSError) as error:
        parser.exit(1, 'Maven preparation failed: ' + str(error) + '\n')


if __name__ == '__main__':
    main()
