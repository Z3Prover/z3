############################################
# Copyright (c) 2026 Microsoft Corporation
# Synthetic archives test repository validation, not native compatibility.
############################################
import copy
import json
from pathlib import Path
import sys
import unittest
from unittest.mock import patch

import test_java_package as fixtures

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / 'java'))
import maven_artifacts
import maven_auto
import maven_bundle as bundle
from mk_java_package import json_bytes, sha256, write_checksums


class MavenBundleTests(unittest.TestCase):
    def setUp(self):
        self.fixture = fixtures.JavaPackagingTests('test_deterministic_outputs_and_exact_resource_set')
        self.fixture.setUp()
        self.addCleanup(self.fixture.doCleanups)
        self.root = self.fixture.root
        self.expected = {'repository': 'example/z3', 'run_id': '123', 'run_attempt': '1',
                         'source_commit': 'a' * 40}
        self.fixture.preparation.update(source_commit='a' * 40, generator_sha256='generator',
                                        loader_sha256='loader', release_runtime_version='5.3.2.0')
        self.packages = self.fixture.build()
        provenance = json.loads((self.packages / 'provenance.json').read_bytes())
        self.identity = {'groupId': 'invalid.z3.prototype', **provenance['distribution']}
        base = self.identity['artifactId'] + '-' + self.identity['version']
        java = {'com/microsoft/z3/Context.java': b'fixture source'}
        sources = fixtures.archive(java)
        javadoc = fixtures.archive({name: b'fixture documentation' for name in (
            'index.html', 'com/microsoft/z3/Context.html', 'com/microsoft/z3/Version.html',
            'com/microsoft/z3/enumerations/Z3_lbool.html')})
        artifacts = {}
        for variant in ('', 'win-x64', 'all'):
            for kind, data in (('', None), ('sources', sources), ('javadoc', javadoc)):
                key = '-'.join(p for p in (variant, kind) if p)
                name = base + ('-' + key if key else '') + '.jar'
                artifacts[key] = name
                if data is not None:
                    (self.packages / name).write_bytes(data)
        self.pom = base + '.pom'
        (self.packages / self.pom).write_text(maven_artifacts.pom_text(self.identity, 'a' * 40), encoding='utf-8')
        self.report = {'prototype': True, 'maven': self.identity, 'input_provenance': provenance,
                       'source_commit': 'a' * 40, 'api_source_commit': 'a' * 40,
                       'runtime_version': '5.3.2.0', 'platforms': ['win-x64'], 'artifacts': artifacts,
                       'jar_sha256': {name: sha256((self.packages / name).read_bytes()) for name in artifacts.values()},
                       'source_validation': {'api_sha256': sha256((self.packages / artifacts['']).read_bytes()),
                                             'files': {name: sha256(data) for name, data in java.items()}}}
        # A prepared Maven family contains its report and POM, not the packer's metadata.
        # Move fixture-only files to another directory instead of deleting them.
        extra = self.root / 'packer-metadata'
        extra.mkdir()
        (self.packages / 'provenance.json').rename(extra / 'provenance.json')
        self.save_report()
        self.repository = self.root / 'repository'
        bundle.prepare_repository(self.packages, self.repository)
        self.consumers = self.root / 'consumers/win-x64'
        self.smokes = self.root / 'smokes/win-x64'
        self.consumers.mkdir(parents=True)
        self.smokes.mkdir(parents=True)
        self.consumer = {'source_commit': 'a' * 40, 'platform': 'win-x64',
                         'preparation_sha256': sha256((self.packages / 'maven-preparation.json').read_bytes()),
                         'repository_sha256': bundle.repository_digest(bundle.repository_files(self.packages, self.report)),
                         'results': {tool + ':' + kind: {'passed': True, 'sources_javadoc_resolved': True,
                             'sha256': self.report['jar_sha256'][artifacts[kind]]}
                             for tool in ('maven', 'gradle') for kind in ('win-x64', 'all')}}
        self.consumer['results']['maven:auto'] = {
            'passed': True, 'sources_javadoc_resolved': True, 'selected_platform': 'win-x64',
            'selector_sha256': sha256(maven_auto.pom(self.report)),
            'sha256': self.report['jar_sha256'][artifacts['win-x64']],
            'unsupported_rejected': True}
        self.smoke = {'source_commit': 'a' * 40, 'generator_sha256': 'generator', 'loader_sha256': 'loader',
                      'platform': 'win-x64', 'passed': True,
                      'artifacts': {kind: {'passed': True, 'jar_name': artifacts[kind],
                          'jar_sha256': self.report['jar_sha256'][artifacts[kind]], 'modes': sorted(bundle.MODES)}
                          for kind in ('win-x64', 'all')}}
        self.save_receipts()

    def save_report(self):
        (self.packages / 'maven-preparation.json').write_bytes(json_bytes(self.report))
        write_checksums(self.packages, 'SHA256SUMS')

    def save_receipts(self):
        (self.consumers / 'receipt.json').write_bytes(json_bytes(self.consumer))
        (self.smokes / 'receipt.json').write_bytes(json_bytes(self.smoke))

    def assemble(self, name='verified', expected=None):
        target = self.root / name
        bundle.bundle(self.packages, self.repository, self.consumers.parent, self.smokes.parent,
                      target, expected or self.expected)
        return target

    def test_repository_and_zip_preserve_bytes_and_are_reproducible(self):
        first, second = self.assemble('first'), self.assemble('second')
        self.assertEqual((first / 'maven-rehearsal.zip').read_bytes(), (second / 'maven-rehearsal.zip').read_bytes())
        entries = bundle.checked_zip((first / 'maven-rehearsal.zip').read_bytes())
        self.assertEqual(len(entries), (len(self.report['artifacts']) + 2) * 5)
        for name in [*self.report['artifacts'].values(), self.pom]:
            path = 'invalid/z3/prototype/z3/' + self.identity['version'] + '/' + name
            self.assertEqual(entries[path], (self.packages / name).read_bytes())
        manifest = json.loads((first / 'rehearsal.json').read_bytes())
        self.assertFalse(manifest['publishable'])
        self.assertFalse(manifest['signed'])
        self.assertEqual(manifest['workflow'], self.expected)

    def test_runtime_pom_cannot_add_platform_dependencies(self):
        path = self.packages / self.pom
        text = path.read_text(encoding='utf-8').replace('</project>', '<dependencies/></project>')
        path.write_text(text, encoding='utf-8')
        self.save_report()
        with self.assertRaisesRegex(ValueError, 'automatic platform dependencies'):
            self.assemble()

    def test_selector_receipt_must_cover_exact_pom_platform_and_failure_behavior(self):
        result = self.consumer['results']['maven:auto']
        for key, value in (('selector_sha256', 'wrong'), ('selected_platform', 'linux-x64'),
                           ('unsupported_rejected', False)):
            original = result[key]
            result[key] = value
            self.save_receipts()
            with self.subTest(key=key), self.assertRaisesRegex(ValueError, 'Automatic selector'):
                self.assemble()
            result[key] = original

    def test_missing_source_or_javadoc_companion_rejected_before_output(self):
        for key in ('sources', 'all-javadoc'):
            original = self.report['artifacts'].pop(key)
            self.save_report()
            with self.subTest(key=key), self.assertRaisesRegex(ValueError, 'artifact family'):
                self.assemble()
            self.report['artifacts'][key] = original
        self.assertFalse((self.root / 'verified').exists())

    def test_unsafe_coordinates_and_classifier_mapping_rejected(self):
        for key, value in (('version', '../escape'), ('artifactId', 'z3/escape'),
                           ('groupId', 'com.microsoft')):
            original = self.report['maven'][key]
            self.report['maven'][key] = value
            self.save_report()
            with self.subTest(key=key), self.assertRaises(ValueError):
                self.assemble()
            self.report['maven'][key] = original
        self.report['artifacts']['all'] = '../outside.jar'
        self.save_report()
        with self.assertRaises(ValueError):
            self.assemble()

    def test_mismatched_pom_and_source_identity_rejected_even_with_new_checksum(self):
        path = self.packages / self.pom
        original = path.read_text(encoding='utf-8')
        for text in (original.replace('<version>', '<version>wrong-'),
                     original.replace('<tag>' + 'a' * 40, '<tag>' + 'b' * 40),
                     original.replace('<name>Z3 Java bindings</name>', '<name/>')):
            path.write_text(text, encoding='utf-8')
            self.save_report()
            with self.assertRaises(ValueError):
                self.assemble()
        path.write_text(original, encoding='utf-8')
        self.report['source_commit'] = 'b' * 40
        self.save_report()
        with self.assertRaisesRegex(ValueError, 'provenance'):
            self.assemble()

    def test_changed_source_body_and_incomplete_javadoc_rejected(self):
        for key, data in (('sources', fixtures.archive({'com/microsoft/z3/Context.java': b'changed'})),
                          ('javadoc', fixtures.archive({'index.html': b'not enough'}))):
            path = self.packages / self.report['artifacts'][key]
            original = path.read_bytes()
            original_hash = self.report['jar_sha256'][path.name]
            path.write_bytes(data)
            self.report['jar_sha256'][path.name] = sha256(data)
            self.save_report()
            with self.subTest(key=key), self.assertRaises(ValueError):
                self.assemble()
            path.write_bytes(original)
            self.report['jar_sha256'][path.name] = original_hash

    def test_duplicate_checksum_and_unexpected_file_rejected(self):
        sums = self.packages / 'SHA256SUMS'
        sums.write_bytes(sums.read_bytes() + sums.read_bytes().splitlines(keepends=True)[0])
        with self.assertRaisesRegex(ValueError, 'duplicate'):
            self.assemble()
        self.save_report()
        (self.packages / 'stale.jar').write_bytes(b'stale')
        with self.assertRaisesRegex(ValueError, 'exact artifact family'):
            self.assemble()

    def test_repository_tampering_and_extra_files_rejected(self):
        path = next(self.repository.rglob('*.sha256'))
        original = path.read_bytes()
        path.write_bytes(b'wrong checksum\n')
        with self.assertRaisesRegex(ValueError, 'Repository bytes'):
            self.assemble()
        path.write_bytes(original)
        (self.repository / 'unexpected.jar').write_bytes(b'stale')
        with self.assertRaisesRegex(ValueError, 'unexpected files'):
            self.assemble()

    def test_consumer_gate_rejects_stale_missing_failed_and_wrong_hash_results(self):
        original = copy.deepcopy(self.consumer)
        changes = [{'preparation_sha256': 'wrong'}, {'repository_sha256': 'wrong'},
                   {'source_commit': 'b' * 40}, {'results': {}},
                   {'results': {**original['results'], 'maven:all': {
                       **original['results']['maven:all'], 'sha256': 'wrong'}}},
                   {'results': {**original['results'], 'gradle:all': {
                       **original['results']['gradle:all'], 'passed': False}}}]
        for change in changes:
            self.consumer = {**original, **change}
            self.save_receipts()
            with self.subTest(change=change), self.assertRaises(ValueError):
                self.assemble()

    def test_smoke_gate_rejects_incomplete_modes_and_wrong_hash(self):
        for key, value in (('modes', ['bundled']), ('jar_sha256', 'wrong'), ('passed', False)):
            original = self.smoke['artifacts']['all'][key]
            self.smoke['artifacts']['all'][key] = value
            self.save_receipts()
            with self.subTest(key=key), self.assertRaises(ValueError):
                self.assemble()
            self.smoke['artifacts']['all'][key] = original

    def test_missing_or_duplicate_platform_consumer_receipts_rejected(self):
        original = self.consumers
        self.consumers = self.root / 'consumers/other'
        self.consumers.mkdir()
        self.save_receipts()
        with self.assertRaisesRegex(ValueError, 'duplicate'):
            self.assemble()
        original.rename(self.root / 'other-consumer')
        self.consumers.rename(self.root / 'last-consumer')
        with self.assertRaisesRegex(ValueError, 'Missing platform'):
            self.assemble()

    def test_source_run_and_attempt_gate(self):
        with self.assertRaisesRegex(ValueError, 'source commit'):
            self.assemble(expected={**self.expected, 'source_commit': 'b' * 40})
        self.report['input_provenance'].update(prototype=False, workflow=self.expected)
        for change in ({'run_id': 'other'}, {'run_attempt': '2'}):
            # Exercise the context gate after family validation. Embedded native
            # provenance validation is independently covered by packaging tests.
            with self.subTest(change=change), patch.object(bundle, 'read_family', return_value=self.report), \
                    self.assertRaisesRegex(ValueError, 'source/run/attempt'):
                self.assemble(expected={**self.expected, **change})


if __name__ == '__main__':
    unittest.main()
