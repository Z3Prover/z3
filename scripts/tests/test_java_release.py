############################################
# Copyright (c) 2026 Microsoft Corporation
# Release safety checks use synthetic binaries; native execution is a CI gate.
############################################
import json
import os
from pathlib import Path
import shutil
import subprocess
import sys
import tempfile
import textwrap
from types import SimpleNamespace
import unittest
from unittest import mock

import test_java_package as fixtures

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / 'java'))
import verify_release
import workflow_inputs
import mk_java_package as package
import smoke


class JavaReleaseTests(unittest.TestCase):
    def setUp(self):
        # Reuse the archive fixture, without inheriting or rerunning its tests.
        self.fixture = fixtures.JavaPackagingTests('test_deterministic_outputs_and_exact_resource_set')
        self.fixture.setUp()
        self.addCleanup(self.fixture.doCleanups)
        self.root = self.fixture.root
        self.expected = {'repository': 'example/z3', 'run_id': '123', 'run_attempt': '1',
                         'source_commit': 'a' * 40}
        self.lock = self.fixture.lock
        self.preparation = self.fixture.preparation
        self.lock.update(input_kind='workflow-artifact', runtime_version='5.3.2.0')
        self.preparation.update(input_kind='workflow-artifact', workflow=self.expected,
                                source_commit='a' * 40, release_runtime_version='5.3.2.0',
                                generator_sha256='generator', loader_sha256='loader')
        self.asset = self.lock['platforms']['win-x64']
        self.asset.update(workflow=self.expected, url='https://github.com/example/z3/actions/runs/123')

    def build(self, directory='release', version='5.3.2', group_id=None, platforms=None):
        return package.assemble(self.lock, self.root, self.fixture.api, self.preparation,
                                self.root / directory, platforms or ['win-x64'],
                                group_id, 'z3', version, release=True)

    def receipt(self, out):
        provenance = smoke.read_provenance(out)
        results = {}
        for classifier in ('win-x64', 'all'):
            jar, _ = smoke.verify_jar(out, provenance, classifier)
            results[classifier] = {'passed': True, 'jar_name': jar.name,
                                   'jar_sha256': package.sha256(jar.read_bytes()),
                                   'modes': sorted(verify_release.MODES)}
        receipt = {key: provenance[key] for key in ('source_commit', 'generator_sha256', 'loader_sha256')}
        receipt.update(platform='win-x64', passed=True, artifacts=results)
        directory = self.root / 'receipts/win-x64'
        directory.mkdir(parents=True)
        path = directory / 'receipt.json'
        path.write_bytes(package.json_bytes(receipt))
        return path, receipt

    def test_release_has_exact_version_no_claimed_namespace_and_reproducible_files(self):
        one, two = self.build('one'), self.build('two')
        self.assertEqual({p.name: p.read_bytes() for p in one.iterdir()},
                         {p.name: p.read_bytes() for p in two.iterdir()})
        provenance = smoke.read_provenance(one)
        self.assertFalse(provenance['prototype'])
        self.assertNotIn('maven', provenance)
        self.assertEqual(provenance['release_tag'], 'z3-5.3.2')
        self.assertEqual({p.name for p in one.iterdir()}, {
            'z3-5.3.2.jar', 'z3-5.3.2-all.jar', 'z3-5.3.2-win-x64.jar',
            'z3-5.3.2-java-provenance.json', 'z3-5.3.2-java-SHA256SUMS'})

    def test_release_rejects_version_drift_and_maven_coordinates(self):
        for kwargs in ({'version': '5.3.3'}, {'version': '5.3.2-SNAPSHOT'},
                       {'group_id': 'com.example'}):
            with self.subTest(kwargs=kwargs), self.assertRaises(ValueError):
                self.build(**kwargs)
        self.assertFalse((self.root / 'release').exists())

    def test_release_rejects_mixed_test_inputs(self):
        for key, value in (('input_kind', 'release-download'), ('source_commit', 'b' * 40),
                           ('release_runtime_version', '5.3.1.0')):
            original = self.preparation[key]
            self.preparation[key] = value
            with self.subTest(key=key), self.assertRaisesRegex(ValueError, 'same source run'):
                self.build()
            self.preparation[key] = original

    def test_release_requires_identical_classes_from_every_platform(self):
        original = self.fixture.api_entries[package.NATIVE_CLASS + '.class']
        self.fixture.api_entries[package.NATIVE_CLASS + '.class'] = original + b'different'
        self.fixture.entries[self.fixture.prefix + 'java/com.microsoft.z3.jar'] = fixtures.archive(self.fixture.api_entries)
        self.fixture.write_release()
        with self.assertRaisesRegex(ValueError, 'classes differ'):
            self.build()

    def test_release_version_is_checked_against_source_before_recording(self):
        args = SimpleNamespace(source_commit='a' * 40, release_version='5.3.3')
        with mock.patch.object(workflow_inputs.subprocess, 'check_output', return_value='a' * 40), \
                mock.patch.object(workflow_inputs, 'source_version', return_value=('5.3.2', '5.3.2.0')):
            with self.assertRaisesRegex(ValueError, 'VERSION.txt'):
                workflow_inputs.context(args)

    def test_release_gate_requires_every_native_receipt(self):
        out = self.build()
        receipts = self.root / 'receipts'
        receipts.mkdir()
        with self.assertRaisesRegex(ValueError, 'Missing native'):
            verify_release.verify(out, receipts, self.root / 'verified', self.expected)

    def test_release_gate_preserves_jars_and_adds_checksummed_validation(self):
        out = self.build()
        self.receipt(out)
        verified = self.root / 'verified'
        verify_release.verify(out, self.root / 'receipts', verified, self.expected)
        for jar in out.glob('*.jar'):
            self.assertEqual(jar.read_bytes(), (verified / jar.name).read_bytes())
        report = verified / 'z3-5.3.2-java-validation.json'
        self.assertTrue(json.loads(report.read_bytes())['passed'])
        sums = (verified / 'z3-5.3.2-java-SHA256SUMS').read_text(encoding='ascii')
        self.assertIn(package.sha256(report.read_bytes()) + '  ' + report.name, sums)

    def test_release_gate_rejects_stale_failed_incomplete_or_wrong_jar_receipts(self):
        out = self.build()
        path, original = self.receipt(out)
        changes = [{'source_commit': 'b' * 40}, {'passed': False},
                   {'artifacts': {'win-x64': original['artifacts']['win-x64']}},
                   {'artifacts': {**original['artifacts'], 'all': {
                       **original['artifacts']['all'], 'jar_sha256': 'wrong'}}},
                   {'artifacts': {**original['artifacts'], 'all': {
                       **original['artifacts']['all'], 'modes': ['bundled']}}}]
        for change in changes:
            path.write_bytes(package.json_bytes({**original, **change}))
            with self.subTest(change=change), self.assertRaises(ValueError):
                verify_release.verify(out, self.root / 'receipts', self.root / 'rejected', self.expected)
            self.assertFalse((self.root / 'rejected').exists())

    def test_release_gate_rejects_different_run_or_attempt(self):
        out = self.build()
        self.receipt(out)
        for change in ({'run_id': 'other'}, {'run_attempt': '2'}):
            with self.subTest(change=change), self.assertRaisesRegex(ValueError, 'source/run/attempt'):
                verify_release.verify(out, self.root / 'receipts', self.root / 'rejected',
                                      {**self.expected, **change})

    def test_release_gate_rejects_unchecksummed_outputs(self):
        out = self.build()
        self.receipt(out)
        (out / 'stale.jar').write_bytes(b'stale')
        with self.assertRaisesRegex(ValueError, 'cover every output'):
            verify_release.verify(out, self.root / 'receipts', self.root / 'rejected', self.expected)


class JavaReleaseWorkflowTests(unittest.TestCase):
    def test_publisher_selects_only_verified_java_attachments(self):
        root = Path(__file__).resolve().parents[2]
        workflow = (root / '.github/workflows/release.yml').read_text(encoding='utf-8')
        publisher = workflow.split('  publish-github:\n', 1)[1].split('  publish-nuget:\n', 1)[0]
        self.assertIn('      java-package\n', publisher.split('    runs-on:', 1)[0])
        script = publisher.split('          find tmp -type f ', 1)[1].split('          # Create release', 1)[0]
        script = 'find tmp -type f ' + textwrap.dedent(script)
        script += '\nprintf "%s\\0" "${unique_files[@]}" > selected.bin\n'
        if os.name == 'nt':
            git = shutil.which('git')
            candidates = [] if not git else [parent / 'bin/bash.exe'
                                             for parent in Path(git).resolve().parents[:3]]
            bash = next((str(path) for path in candidates if path.is_file()), None)
        else:
            bash = shutil.which('bash')
        if not bash or not Path(bash).is_file():
            self.skipTest('Bash is required to exercise the release collector')
        with tempfile.TemporaryDirectory() as temporary:
            directory = Path(temporary)
            selected = ['java-release-packages/z3-5.3.2.jar',
                        'java-release-packages/z3-5.3.2-all.jar',
                        'java-release-packages/z3-5.3.2-java-provenance.json',
                        'java-release-packages/z3-5.3.2-java-validation.json',
                        'java-release-packages/z3-5.3.2-java-SHA256SUMS',
                        'UbuntuBuild/native distribution.zip']
            rejected = ['java-assembled-packages/unverified.jar',
                        'java-assembled-packages/z3-5.3.2-java-provenance.json',
                        'java-release-smoke-win-x64/receipt.json', 'UbuntuBuild/receipt-linux-x64.json']
            for name in selected + rejected:
                path = directory / 'tmp' / name
                path.parent.mkdir(parents=True, exist_ok=True)
                path.write_bytes(b'collector fixture')
            path = directory / 'collect.sh'
            path.write_text('#!/usr/bin/env bash\nset -euo pipefail\n' + script, encoding='utf-8', newline='\n')
            result = subprocess.run([bash, path.name], cwd=directory, capture_output=True, text=True)
            self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
            actual = (directory / 'selected.bin').read_bytes().decode().rstrip('\0').split('\0')
            self.assertEqual(set(actual), {'tmp/' + name for name in selected})


if __name__ == '__main__':
    unittest.main()
