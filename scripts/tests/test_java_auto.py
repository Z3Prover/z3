############################################
# Copyright (c) 2026 Microsoft Corporation
# Check published selector metadata, not native compatibility.
############################################
from pathlib import Path
import os
import sys
import tempfile
import unittest
from xml.etree import ElementTree as ET

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / 'java'))
import maven_artifacts
import maven_auto
import maven_consumer


class MavenAutoTests(unittest.TestCase):
    def setUp(self):
        self.report = {'maven': {'groupId': 'invalid.z3.prototype', 'artifactId': 'z3', 'version': '1-test'},
                       'source_commit': 'a' * 40, 'platforms': ['linux-x64', 'linux-arm64', 'win-x64', 'osx-arm64']}
        self.ns = {'m': maven_artifacts.NS}

    def text(self, root, path):
        return root.findtext('/'.join('m:' + part for part in path.split('/')), namespaces=self.ns)

    def test_pom_only_selector_has_one_runtime_dependency_and_no_publish_configuration(self):
        root = ET.fromstring(maven_auto.pom(self.report))
        for key, value in {'groupId': 'invalid.z3.prototype', 'artifactId': 'z3-auto',
                           'version': '1-test', 'packaging': 'pom', 'scm/tag': 'a' * 40}.items():
            self.assertEqual(self.text(root, key), value)
        deps = root.findall('m:dependencies/m:dependency', self.ns)
        self.assertEqual(len(deps), 1)
        self.assertEqual(self.text(deps[0], 'artifactId'), 'z3')
        self.assertEqual(self.text(deps[0], 'classifier'), '${z3.platform}')
        self.assertIsNone(root.find('m:build', self.ns))
        self.assertIsNone(root.find('m:distributionManagement', self.ns))
        self.assertEqual(self.text(root, 'properties/z3.platform'), maven_auto.UNSUPPORTED)

    def test_profiles_match_explicit_jvm_aliases_and_only_shipped_platforms(self):
        root = ET.fromstring(maven_auto.pom(self.report))
        matches = {}
        for profile in root.findall('m:profiles/m:profile', self.ns):
            platform = self.text(profile, 'properties/z3.platform')
            matches.setdefault(platform, set()).add(self.text(profile, 'activation/os/arch'))
            self.assertIsNone(profile.find('m:activation/m:property', self.ns))
            field = 'name' if platform.startswith('linux-') else 'family'
            self.assertEqual(self.text(profile, 'activation/os/' + field),
                             {'linux-x64': 'Linux', 'linux-arm64': 'Linux',
                              'win-x64': 'Windows', 'osx-arm64': 'Mac'}[platform])
        self.assertEqual(matches, {'linux-x64': {'amd64', 'x86_64', 'x64'},
                                  'linux-arm64': {'aarch64', 'arm64'},
                                  'win-x64': {'amd64', 'x86_64', 'x64'},
                                  'osx-arm64': {'aarch64', 'arm64'}})
        self.report['platforms'] = ['win-x64']
        windows = ET.fromstring(maven_auto.pom(self.report))
        self.assertEqual({self.text(p, 'properties/z3.platform')
                          for p in windows.findall('m:profiles/m:profile', self.ns)}, {'win-x64'})

    def test_selector_is_deterministic_and_does_not_modify_runtime_pom(self):
        original = maven_artifacts.pom_text(self.report['maven'], self.report['source_commit'])
        first = maven_auto.pom(self.report)
        self.report['platforms'].reverse()
        self.report['maven'] = dict(reversed(list(self.report['maven'].items())))
        self.assertEqual(first, maven_auto.pom(self.report))
        self.assertEqual(original, maven_artifacts.pom_text(self.report['maven'], self.report['source_commit']))
        runtime = ET.fromstring(original)
        self.assertIsNone(runtime.find('m:dependencies', self.ns))
        self.assertIsNone(runtime.find('m:profiles', self.ns))

    def test_consumer_rejects_extra_jars_and_unexpected_selector_metadata(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            jar, extra, pom = root / 'runtime.jar', root / 'extra.jar', root / 'selector.pom'
            jar.write_bytes(b'runtime')
            extra.write_bytes(b'other API classes')
            pom.write_bytes(maven_auto.pom(self.report))
            classpath = os.pathsep.join(str(p) for p in (pom, jar))
            self.assertEqual(maven_consumer.maven_runtime(classpath, self.report, selector=True), jar)
            for invalid, selector in ((classpath, False), (classpath + os.pathsep + str(extra), True),
                                      (str(jar), True)):
                with self.subTest(classpath=invalid), self.assertRaisesRegex(ValueError, 'exactly one runtime'):
                    maven_consumer.maven_runtime(invalid, self.report, selector=selector)
            pom.write_bytes(b'other POM')
            with self.assertRaisesRegex(ValueError, 'exactly one runtime'):
                maven_consumer.maven_runtime(classpath, self.report, selector=True)


if __name__ == '__main__':
    unittest.main()
