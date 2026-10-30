############################################
# Copyright (c) 2026 Microsoft Corporation
# Exercise real Maven/Gradle resolution from an isolated file repository.
############################################
import argparse
import json
import os
from pathlib import Path
import shutil
from xml.sax.saxutils import escape

from prepare import run, SCRIPTS
from mk_java_package import LIBRARIES, json_bytes, sha256
import maven_auto


def check_resolved(paths, packages, report, classifier):
    expected = [report['artifacts'][key] for key in
                (classifier, classifier + '-sources', classifier + '-javadoc')]
    if len(paths) != 3 or {sha256(Path(p).read_bytes()) for p in paths} != {
            report['jar_sha256'][name] for name in expected}:
        raise ValueError('Consumer resolved incorrect binary/source/Javadoc artifacts')
    for name in expected:
        if sha256((packages / name).read_bytes()) != report['jar_sha256'][name]:
            raise ValueError('Prepared Maven artifact changed: ' + name)


def maven_runtime(classpath, report, selector=False):
    paths = [Path(p) for p in classpath.strip().split(os.pathsep)]
    jars = [p for p in paths if p.suffix == '.jar']
    metadata = [p for p in paths if p.suffix != '.jar']
    # dependency:build-classpath also lists an explicitly requested POM. It
    # contains no Java classes; allow only this exact selector metadata.
    if (len(jars) != 1 or len(metadata) != int(selector)
            or any(p.suffix != '.pom' or sha256(p.read_bytes()) != sha256(maven_auto.pom(report))
                   for p in metadata)):
        raise ValueError('Maven must resolve exactly one runtime JAR and only the requested selector POM')
    return jars[0]


def consume(packages, platform, work, mvn, gradle=None, repository=None):
    packages, work = packages.resolve(), work.resolve()
    report = json.loads((packages / 'maven-preparation.json').read_bytes())
    if report['maven']['groupId'] != 'invalid.z3.prototype' or not report['prototype']:
        raise ValueError('Consumer test accepts only unpublished test coordinates')
    if platform not in report['platforms']:
        raise ValueError('Consumer platform absent from prepared family')
    for line in (packages / 'SHA256SUMS').read_text(encoding='ascii').splitlines():
        digest, name = line.split('  ', 1)
        if Path(name).name != name or sha256((packages / name).read_bytes()) != digest:
            raise ValueError('Consumer input checksum mismatch: ' + name)
    work.mkdir(parents=True, exist_ok=False)
    settings = work / 'settings.xml'
    settings.write_text('<settings xmlns="http://maven.apache.org/SETTINGS/1.2.0"/>', encoding='utf-8')
    identity = report['maven']
    maven = [mvn, '-B', '-ntp', '-s', settings, '-Dmaven.repo.local=' + str(work / 'maven-cache')]
    from maven_bundle import check_repository, prepare_repository, read_family
    if repository is None:
        repository = work / 'repository'
        prepare_repository(packages, repository)
    repository = repository.resolve()
    repository_sha = check_repository(repository, packages, read_family(packages))
    results = {}
    for tool in ['maven'] + (['gradle'] if gradle else []):
        for classifier in (platform, 'all') + (('auto',) if tool == 'maven' else ()):
            selected = platform if classifier == 'auto' else classifier
            project = work / (tool + '-' + classifier)
            source = project / 'src/main/java'
            source.mkdir(parents=True)
            shutil.copyfile(SCRIPTS / 'java/Smoke.java', source / 'Smoke.java')
            coordinate = ':'.join(identity[key] for key in ('groupId', 'artifactId', 'version'))
            if tool == 'maven':
                dependency = '<groupId>{groupId}</groupId><artifactId>{artifactId}</artifactId><version>{version}</version>'.format(**identity)
                items = ''.join('<artifactItem>' + dependency + '<classifier>' + selected + '-' + kind
                                + '</classifier><type>jar</type></artifactItem>' for kind in ('sources', 'javadoc'))
                requested = (('<groupId>{groupId}</groupId><artifactId>{artifactId}</artifactId>'
                              '<version>{version}</version><type>pom</type>').format(**maven_auto.identity(report))
                             if classifier == 'auto' else dependency + '<classifier>' + classifier + '</classifier>')
                pom = '''<project><modelVersion>4.0.0</modelVersion><groupId>invalid.z3.consumer</groupId>
<artifactId>consumer</artifactId><version>1</version><properties><maven.compiler.release>8</maven.compiler.release>
<project.build.sourceEncoding>UTF-8</project.build.sourceEncoding></properties>
<repositories><repository><id>test-files</id><url>{url}</url></repository></repositories>
<dependencies><dependency>{requested}</dependency></dependencies>
<build><plugins><plugin><groupId>org.apache.maven.plugins</groupId><artifactId>maven-dependency-plugin</artifactId>
<version>3.9.0</version><configuration><outputFile>${{project.basedir}}/classpath.txt</outputFile>
<outputDirectory>${{project.basedir}}/companions</outputDirectory><artifactItems>{items}</artifactItems></configuration>
</plugin></plugins></build></project>'''.format(url=escape(repository.as_uri()), requested=requested, items=items)
                (project / 'pom.xml').write_text(pom, encoding='utf-8')
                run([*maven, '-f', project / 'pom.xml',
                     'org.apache.maven.plugins:maven-compiler-plugin:3.16.0:compile',
                     'org.apache.maven.plugins:maven-dependency-plugin:3.9.0:build-classpath',
                     'org.apache.maven.plugins:maven-dependency-plugin:3.9.0:copy'])
                classpath = (project / 'classpath.txt').read_text(encoding='utf-8').strip()
                jar = maven_runtime(classpath, report, selector=classifier == 'auto')
                resolved = [jar, *sorted((project / 'companions').glob('*.jar'))]
                classes = project / 'target/classes'
            else:
                (project / 'settings.gradle').write_text("rootProject.name = 'z3-consumer'\n", encoding='utf-8')
                build = '''plugins { id 'java' }
repositories { maven { url = uri(%s) } }
configurations { companions }
dependencies {
    implementation %s
    companions %s
    companions %s
}
tasks.withType(JavaCompile).configureEach { options.release = 8 }
tasks.register('resolved') {
    dependsOn classes
    doLast {
        file('resolved.json').text = groovy.json.JsonOutput.toJson(
            [binary: configurations.runtimeClasspath.singleFile.absolutePath,
             companions: configurations.companions.files.collect { it.absolutePath }])
    }
}
''' % tuple(json.dumps(value) for value in (repository.as_uri(), coordinate + ':' + classifier,
                                           coordinate + ':' + classifier + '-sources', coordinate + ':' + classifier + '-javadoc'))
                (project / 'build.gradle').write_text(build, encoding='utf-8')
                run([gradle, '--no-daemon', '--console=plain', '-p', project, 'resolved'])
                resolution = json.loads((project / 'resolved.json').read_bytes())
                jar = Path(resolution['binary'])
                classpath = str(jar)
                resolved = [jar, *resolution['companions']]
                classes = project / 'build/classes/java/main'
            check_resolved(resolved, packages, report, selected)
            empty, temporary = project / 'empty-native-path', project / 'native-temp'
            empty.mkdir()
            temporary.mkdir()
            # Child JVM has an empty explicit JNI path. Smoke asserts extraction
            # of exactly the current platform's two libraries as well as SAT/UNSAT.
            output = run(['java', '-Djava.library.path=' + str(empty), '-Djava.io.tmpdir=' + str(temporary),
                          '-cp', str(classes) + os.pathsep + classpath, 'Smoke', 'bundled',
                          report['runtime_version'], ','.join(LIBRARIES[platform.split('-')[0]])])
            if 'PASS bundled' not in output:
                raise ValueError('Consumer did not report native success')
            results[tool + ':' + classifier] = {'passed': True, 'sha256': sha256(jar.read_bytes()),
                                                'sources_javadoc_resolved': True}
            if classifier == 'auto':
                # Both ordinary forms have already populated this isolated
                # cache. Offline checks cannot fetch an unrelated remote JAR.
                command = [*maven, '-o', '-f', project / 'pom.xml',
                           'org.apache.maven.plugins:maven-dependency-plugin:3.9.0:build-classpath',
                           '-Dmdep.regenerateFile=true']
                original_classpath = (project / 'classpath.txt').read_bytes()
                run([*command, '-Dz3.platform=all'])
                override = maven_runtime((project / 'classpath.txt').read_text(encoding='utf-8'),
                                         report, selector=True)
                if (sha256(override.read_bytes())
                        != report['jar_sha256'][report['artifacts']['all']]):
                    raise ValueError('Explicit target platform did not override host detection')
                try:
                    run([*command, '-Dz3.platform=unsupported-platform-test'])
                except ValueError as error:
                    if 'unsupported-platform-test' not in str(error):
                        raise
                else:
                    raise ValueError('Unsupported platform unexpectedly resolved a runtime JAR')
                (project / 'classpath.txt').write_bytes(original_classpath)
                results['maven:auto'].update(selected_platform=platform,
                    selector_sha256=sha256(maven_auto.pom(report)),
                    override_checked=True, unsupported_rejected=True)
            print('PASS consumer', tool, classifier, flush=True)
    (work / 'receipt.json').write_bytes(json_bytes({'source_commit': report['source_commit'],
                                                   'platform': platform, 'results': results,
                                                   'repository_sha256': repository_sha,
                                                   'preparation_sha256': sha256((packages / 'maven-preparation.json').read_bytes())}))


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('--packages', type=Path, required=True)
    parser.add_argument('--platform', required=True)
    parser.add_argument('--work-dir', type=Path, required=True)
    parser.add_argument('--repository', type=Path, help='Resolve from an already prepared local repository')
    parser.add_argument('--mvn', default=shutil.which('mvn') or shutil.which('mvn.cmd'))
    parser.add_argument('--gradle', nargs='?', const='auto', help='Also test Gradle; optionally pass its executable path')
    args = parser.parse_args()
    try:
        if not args.mvn:
            raise ValueError('Maven executable missing')
        if args.gradle == 'auto':
            args.gradle = shutil.which('gradle') or shutil.which('gradle.bat')
            if not args.gradle:
                raise ValueError('Gradle executable missing')
        consume(args.packages, args.platform, args.work_dir, args.mvn, args.gradle, args.repository)
    except (OSError, KeyError, ValueError) as error:
        parser.exit(1, 'Maven/Gradle consumer failed: ' + str(error) + '\n')


if __name__ == '__main__':
    main()
