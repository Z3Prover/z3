############################################
# Copyright (c) 2026 Microsoft Corporation
############################################
import json
from pathlib import Path
import sys
import tempfile
import unittest
from unittest.mock import patch
from xml.etree import ElementTree as ET

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / 'java'))
import maven_artifacts
import maven_consumer
import sources
import test_java_package as fixtures


class MavenPreparationTests(unittest.TestCase):
    def test_pom_has_metadata_without_claiming_official_coordinates(self):
        root = ET.fromstring(maven_artifacts.pom_text(
            {'groupId': 'invalid.z3.prototype', 'artifactId': 'z3', 'version': '5.3.2-test'}, 'a' * 40))
        ns = {'m': maven_artifacts.NS}
        for path in ('groupId', 'artifactId', 'version', 'name', 'description', 'url',
                     'licenses/license/name', 'licenses/license/url', 'developers/developer/name',
                     'scm/connection', 'scm/developerConnection', 'scm/url', 'scm/tag'):
            self.assertTrue(root.find('/'.join('m:' + p for p in path.split('/')), ns).text)
        self.assertEqual(root.find('m:groupId', ns).text, 'invalid.z3.prototype')
        self.assertIsNone(root.find('m:distributionManagement', ns))

    def test_signature_comparison_preserves_descriptors_ignores_member_order(self):
        first = 'public class A {\n  public void f();\n    descriptor: ()V\n\n  int x;\n    descriptor: I\n}\n'
        reordered = 'public class A {\n  int x;\n    descriptor: I\n\n  public void f();\n    descriptor: ()V\n}\n'
        self.assertEqual(sources.canonical_signatures(first), sources.canonical_signatures(reordered))
        self.assertNotEqual(sources.canonical_signatures(first),
                            sources.canonical_signatures(reordered.replace('()V', '(I)V')))
        with self.assertRaises(ValueError):
            sources.canonical_signatures('not javap output')

    def test_sources_follow_shipped_api_and_keep_generated_and_loader_files(self):
        with tempfile.TemporaryDirectory() as temp:
            root = Path(temp)
            java = root / 'src/api/java'
            java.mkdir(parents=True)
            for name in ('Context', 'NotInJar', 'NativeLibraryLoader'):
                (java / (name + '.java')).write_text(name, encoding='utf-8')
            generated = root / 'generated'
            (generated / 'enumerations').mkdir(parents=True)
            (generated / 'Native.java').write_text('generated Native', encoding='utf-8')
            (generated / 'enumerations/Z3_lbool.java').write_text('generated enum', encoding='utf-8')
            api = root / 'api.jar'
            api.write_bytes(fixtures.archive({'com/microsoft/z3/Context.class': b'fixture'}))
            with patch.object(sources, 'run'):
                out = sources.collect(root, [], generated, java / 'NativeLibraryLoader.java', root / 'out', api)
            self.assertEqual({p.relative_to(out).as_posix() for p in out.rglob('*.java')}, {
                'com/microsoft/z3/Context.java', 'com/microsoft/z3/Native.java',
                'com/microsoft/z3/NativeLibraryLoader.java', 'com/microsoft/z3/enumerations/Z3_lbool.java'})

    def test_changed_or_missing_consumer_artifact_is_rejected(self):
        with tempfile.TemporaryDirectory() as temp:
            root = Path(temp)
            names = {'all': 'binary.jar', 'all-sources': 'source.jar', 'all-javadoc': 'doc.jar'}
            for name in names.values():
                (root / name).write_bytes(name.encode('ascii'))
            report = {'artifacts': names, 'jar_sha256': {
                name: maven_consumer.sha256((root / name).read_bytes()) for name in names.values()}}
            paths = [root / name for name in names.values()]
            maven_consumer.check_resolved(paths, root, report, 'all')
            with self.assertRaises(ValueError):
                maven_consumer.check_resolved(paths[:-1], root, report, 'all')
            (root / 'binary.jar').write_bytes(b'changed')
            with self.assertRaises(ValueError):
                maven_consumer.check_resolved(paths, root, report, 'all')

    def test_source_downloads_include_all_pinned_handwritten_files(self):
        lock = json.loads((sources.SCRIPTS / 'java/release.json').read_bytes())
        java = [name for name in lock['sources'] if name.endswith('.java')]
        self.assertGreater(len(java), 70)
        self.assertIn('src/api/java/Context.java', java)
        self.assertTrue(all(len(lock['sources'][name]['sha256']) == 64 for name in java))


if __name__ == '__main__':
    unittest.main()
