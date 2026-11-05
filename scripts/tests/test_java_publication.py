############################################
# Copyright (c) 2026 Microsoft Corporation
# Synthetic archives verify publication gates, not native solver execution.
############################################
import json
from pathlib import Path
import sys
import unittest
from unittest.mock import patch
import urllib.error

import test_java_bundle
sys.path.insert(0, str(Path(__file__).resolve().parents[1] / 'java'))
import maven_artifacts
import maven_bundle
import maven_publication as publication
from mk_java_package import checked_zip, json_bytes, sha256


class PublicationConfigurationTests(unittest.TestCase):
    def test_disabled_requires_no_credentials_or_coordinates(self):
        self.assertIn('SKIP', publication.preflight('disabled', '', '', {}))

    def test_enabled_requires_all_credentials_and_upstream_dispatch(self):
        env = {'GITHUB_REPOSITORY': 'Z3Prover/z3', 'GITHUB_EVENT_NAME': 'workflow_dispatch'}
        for mode in ('validate', 'publish'):
            with self.subTest(mode=mode), self.assertRaisesRegex(ValueError, 'CENTRAL_USERNAME.*MAVEN_GPG_PASSPHRASE'):
                publication.preflight(mode, 'org.fixture.z3', 'z3', env)
        env.update({key: 'fixture-secret' for key in ('CENTRAL_USERNAME', 'CENTRAL_PASSWORD',
                                                    'MAVEN_GPG_KEY', 'MAVEN_GPG_PASSPHRASE')})
        self.assertIn('validate', publication.preflight('validate', 'org.fixture.z3', 'z3', env))
        for change in ({'GITHUB_REPOSITORY': 'example/z3'}, {'GITHUB_EVENT_NAME': 'pull_request'}):
            with self.subTest(change=change), self.assertRaisesRegex(ValueError, 'upstream release'):
                publication.preflight('publish', 'org.fixture.z3', 'z3', {**env, **change})

    def test_test_coordinates_and_unsafe_groups_are_rejected(self):
        for group in ('invalid.z3.prototype', 'example.z3', '../../z3', 'com.microsoft/z3', 'org..z3'):
            with self.subTest(group=group), self.assertRaises(ValueError):
                publication.preflight('publish', group, 'z3', {})

    def test_existing_version_and_network_error_do_not_become_skip(self):
        for code in (403, 429, 500):
            error = urllib.error.HTTPError('https://example.invalid', code, 'fixture', {}, None)
            with self.subTest(code=code), patch.object(publication, 'repository_files', return_value={'a.pom': b''}), \
                    patch.object(publication.urllib.request, 'urlopen', side_effect=error), \
                    self.assertRaisesRegex(ValueError, str(code)):
                publication.require_unpublished(Path('.'), {})
            error.close()
        with patch.object(publication, 'repository_files', return_value={'a.pom': b''}), \
                patch.object(publication.urllib.request, 'urlopen'), \
                self.assertRaisesRegex(ValueError, 'already published'):
            publication.require_unpublished(Path('.'), {})
        error.close()
        error = urllib.error.HTTPError('https://example.invalid', 404, 'fixture', {}, None)
        with patch.object(publication, 'repository_files', return_value={'a.pom': b''}), \
                patch.object(publication.urllib.request, 'urlopen', side_effect=error):
            publication.require_unpublished(Path('.'), {})


class PublicationInputTests(unittest.TestCase):
    def setUp(self):
        self.fixture = test_java_bundle.MavenBundleTests('test_repository_and_zip_preserve_bytes_and_are_reproducible')
        self.fixture.setUp()
        self.addCleanup(self.fixture.doCleanups)
        self.rehearsal = self.fixture.assemble()

    def verify(self, expected=None, production=False):
        return publication.verified_inputs(self.fixture.packages, self.rehearsal,
            maven_artifacts.TEST_GROUP, expected or self.fixture.expected, production)

    def test_exact_verified_bundle_accepted_for_offline_preparation(self):
        self.assertEqual(self.verify(), self.fixture.report)

    def test_changed_run_commit_or_bundle_rejected(self):
        for key in ('run_id', 'run_attempt', 'source_commit'):
            with self.subTest(key=key), self.assertRaisesRegex(ValueError, 'exact verified'):
                self.verify({**self.fixture.expected, key: 'different'})
        target = self.rehearsal / 'maven-rehearsal.zip'
        target.write_bytes(target.read_bytes() + b'changed')
        with self.assertRaisesRegex(ValueError, 'exact verified'):
            self.verify()

    def test_serialized_receipts_are_revalidated(self):
        target = self.rehearsal / 'rehearsal.json'
        manifest = json.loads(target.read_bytes())
        manifest['validation']['consumers']['win-x64']['results']['maven:auto']['selector_sha256'] = 'wrong'
        target.write_bytes(json_bytes(manifest))
        with self.assertRaisesRegex(ValueError, 'Automatic selector'):
            self.verify()

    def test_prototype_cannot_enter_production_deployment(self):
        with self.assertRaisesRegex(ValueError, 'current-source'):
            self.verify(production=True)

    def test_explicit_group_is_validated_before_consumer_resolution(self):
        fixture = self.fixture
        group = 'invalid.z3.configured'
        fixture.report['maven']['groupId'] = group
        (fixture.packages / fixture.pom).write_text(maven_artifacts.pom_text(
            fixture.report['maven'], fixture.report['source_commit']), encoding='utf-8')
        fixture.save_report()
        with self.assertRaisesRegex(ValueError, 'selected unpublished coordinates'):
            maven_bundle.read_family(fixture.packages)
        self.assertEqual(maven_bundle.read_family(fixture.packages, group)['maven']['groupId'], group)
        files = maven_bundle.repository_files(fixture.packages, fixture.report)
        self.assertTrue(all(name.startswith('invalid/z3/configured/') for name in files))

    def test_snapshot_rehearsal_preserves_payloads_and_never_calls_upload_plugin(self):
        out = self.fixture.root / 'central'
        staging = out / 'central-staging'
        staging.mkdir(parents=True)
        files = maven_bundle.repository_files(self.fixture.packages, self.fixture.report)
        for name, value in files.items():
            path = staging / name
            path.parent.mkdir(parents=True, exist_ok=True)
            path.write_bytes(value)
        (out / 'inputs.json').write_bytes(json_bytes({'maven': self.fixture.identity}))
        with patch.object(publication, 'run', side_effect=AssertionError('must not upload')):
            publication.central(out, 'unused-mvn', 'disabled')
            data = (out / 'target/central-publishing/central-bundle.zip').read_bytes()
            self.assertEqual(checked_zip(data), files)
            receipt = json.loads((out / 'publication.json').read_bytes())
            self.assertFalse(receipt['uploaded'])
            self.assertEqual(receipt['bundle_sha256'], sha256(data))
            with self.assertRaisesRegex(ValueError, 'Snapshot'):
                publication.central(out, 'unused-mvn', 'publish')


if __name__ == '__main__':
    unittest.main()
