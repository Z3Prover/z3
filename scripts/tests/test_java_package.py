############################################
# Copyright (c) 2026 Microsoft Corporation
# Synthetic package fixtures; native execution is covered by scripts/java/smoke.py.
############################################
import io
import json
from pathlib import Path
import struct
import sys
import tempfile
import unittest
import warnings
import zipfile
from unittest import mock

sys.path.insert(0, str(Path(__file__).resolve().parents[1]))
import mk_java_package as package
sys.path.insert(0, str(Path(__file__).resolve().parents[1] / 'java'))
import workflow_inputs
import smoke as java_smoke


def archive(entries):
    stream = io.BytesIO()
    with zipfile.ZipFile(stream, 'w') as output:
        for name, data in entries.items():
            output.writestr(name, data)
    return stream.getvalue()


def pe(machine=0x8664):
    data = bytearray(128)
    data[:2] = b'MZ'
    struct.pack_into('<I', data, 60, 80)
    data[80:84] = b'PE\0\0'
    struct.pack_into('<H', data, 84, machine)
    return bytes(data)


class JavaPackagingTests(unittest.TestCase):
    def setUp(self):
        self.temp = tempfile.TemporaryDirectory()
        self.addCleanup(self.temp.cleanup)
        self.root = Path(self.temp.name)
        self.name = 'z3-5.3.2-x64-win.zip'
        self.prefix = self.name[:-4] + '/'
        header = b'\xca\xfe\xba\xbe\0\0\0\x34'
        self.api_entries = {package.NATIVE_CLASS + '.class': header,
                            'com/microsoft/z3/Context.class': header,
                            package.LOADER_CLASS: header}
        self.api = archive(self.api_entries)
        self.entries = {self.prefix + 'java/com.microsoft.z3.jar': self.api,
                        self.prefix + 'LICENSE.txt': b'Synthetic MIT fixture',
                        self.prefix + 'bin/libz3.dll': pe(),
                        self.prefix + 'bin/z3java.dll': pe()}
        self.lock = {'version': '5.3.2', 'tag': 'z3-5.3.2', 'commit': 'a' * 40,
                     'platforms': {'win-x64': {'name': self.name,
                         'url': 'https://github.com/Z3Prover/z3/releases/download/z3-5.3.2/' + self.name}}}
        self.preparation = {'release_commit': 'a' * 40, 'release_version': '5.3.2',
                            'api_sha256': package.sha256(self.api), 'synthetic_fixture': True}
        self.write_release()

    def write_release(self):
        data = archive(self.entries)
        (self.root / self.name).write_bytes(data)
        self.lock['platforms']['win-x64']['sha256'] = package.sha256(data)

    def build(self, directory='out', platforms=None):
        return package.assemble(self.lock, self.root, self.api, self.preparation,
                                self.root / directory, ['win-x64'] if platforms is None else platforms,
                                'invalid.z3.prototype', 'z3', '5.3.2-packaging-SNAPSHOT')

    def add_unix_platform(self, classifier):
        if classifier == 'linux-x64':
            data = bytearray(64)
            data[:6] = b'\x7fELF\x02\x01'
            struct.pack_into('<H', data, 18, 62)
            binary = bytes(data)
        else:
            binary = b'\xcf\xfa\xed\xfe' + struct.pack('<I', 0x100000c) + bytes(24)
        name = 'z3-5.3.2-' + classifier + '.zip'
        prefix = name[:-4] + '/'
        entries = {prefix + 'java/com.microsoft.z3.jar': self.api,
                   prefix + 'LICENSE.txt': ('Synthetic MIT fixture for ' + classifier).encode('ascii')}
        entries.update({prefix + 'bin/' + library: binary for library in
                        package.LIBRARIES[classifier.split('-')[0]]})
        data = archive(entries)
        (self.root / name).write_bytes(data)
        self.lock['platforms'][classifier] = {
            'name': name, 'sha256': package.sha256(data),
            'url': 'https://github.com/Z3Prover/z3/releases/download/z3-5.3.2/' + name}
        return entries

    def test_universal_contains_exact_platform_union_and_one_api(self):
        sources = {'win-x64': self.entries,
                   'linux-x64': self.add_unix_platform('linux-x64'),
                   'osx-arm64': self.add_unix_platform('osx-arm64')}
        out = self.build(platforms=list(sources))
        provenance = json.loads((out / 'provenance.json').read_bytes())
        jar, universal = java_smoke.verify_jar(out, provenance, 'all')
        union = {}
        for classifier in sources:
            _, platform = java_smoke.verify_jar(out, provenance, classifier)
            union.update({k: v for k, v in platform.items() if k.startswith(package.RESOURCE_PREFIX)})
            license_text = next(v for k, v in sources[classifier].items() if k.endswith('/LICENSE.txt'))
            self.assertEqual(universal['META-INF/z3/licenses/' + classifier + '.txt'], license_text)
        self.assertEqual({k: v for k, v in universal.items() if k.startswith(package.RESOURCE_PREFIX)}, union)
        self.assertEqual(len(union), 6)
        self.assertEqual({k: v for k, v in universal.items() if k.endswith('.class')}, self.api_entries)
        embedded = json.loads(universal['META-INF/z3/provenance.json'])
        self.assertEqual(set(embedded['platforms']), set(sources))
        self.assertEqual(provenance['platforms'], sorted(sources))
        self.assertIn(package.sha256(jar.read_bytes()) + '  ' + jar.name,
                      (out / 'SHA256SUMS').read_text(encoding='ascii'))

    def test_universal_deterministic_when_platform_selection_is_reordered(self):
        self.add_unix_platform('linux-x64')
        first = self.build('one', ['win-x64', 'linux-x64'])
        second = self.build('two', ['linux-x64', 'win-x64'])
        self.assertEqual({p.name: p.read_bytes() for p in first.iterdir()},
                         {p.name: p.read_bytes() for p in second.iterdir()})

    def test_universal_requires_every_selected_platform_before_writing(self):
        self.add_unix_platform('linux-x64')
        for change in ('missing', 'wrong-cpu'):
            with self.subTest(change=change):
                if change == 'missing':
                    del self.entries[self.prefix + 'bin/z3java.dll']
                else:
                    self.entries[self.prefix + 'bin/z3java.dll'] = pe(0xaa64)
                self.write_release()
                with self.assertRaises(ValueError):
                    self.build(platforms=['linux-x64', 'win-x64'])
                self.assertFalse((self.root / 'out').exists())

    def test_universal_rejects_modified_resources_manifests_and_classes(self):
        self.add_unix_platform('linux-x64')
        out = self.build(platforms=['linux-x64', 'win-x64'])
        provenance = json.loads((out / 'provenance.json').read_bytes())
        jar, original = java_smoke.verify_jar(out, provenance, 'all')
        resource = package.RESOURCE_PREFIX + 'win-x64/z3java.dll'
        for change in ('missing-resource', 'wrong-binary', 'extra-resource', 'missing-platform', 'extra-platform', 'wrong-api'):
            entries = dict(original)
            manifest = json.loads(entries['META-INF/z3/provenance.json'])
            if change == 'missing-resource':
                del entries[resource]
            elif change == 'wrong-binary':
                entries[resource] = b'not the original native library'
            elif change == 'extra-resource':
                entries[package.RESOURCE_PREFIX + 'osx-arm64/libz3.dylib'] = b'not selected'
            elif change == 'missing-platform':
                del manifest['platforms']['win-x64']
            elif change == 'extra-platform':
                manifest['platforms']['osx-arm64'] = manifest['platforms']['win-x64']
            elif change == 'wrong-api':
                entries[package.NATIVE_CLASS + '.class'] += b'different'
            entries['META-INF/z3/provenance.json'] = package.json_bytes(manifest)
            jar.write_bytes(archive(entries))
            with self.subTest(change=change), self.assertRaises(ValueError):
                java_smoke.verify_jar(out, provenance, 'all')

    def test_empty_and_unknown_platform_selection(self):
        for platforms in ([], ['all'], ['linux-unknown']):
            with self.subTest(platforms=platforms), self.assertRaises(ValueError):
                self.build(platforms=platforms)

    def test_deterministic_outputs_and_exact_resource_set(self):
        first, second = self.build('one'), self.build('two')
        self.assertEqual({p.name: p.read_bytes() for p in first.iterdir()},
                         {p.name: p.read_bytes() for p in second.iterdir()})
        jar = next(first.glob('*-win-x64.jar'))
        entries = package.checked_zip(jar.read_bytes())
        resources = {name for name in entries if name.startswith(package.RESOURCE_PREFIX)}
        self.assertEqual(resources, {package.RESOURCE_PREFIX + 'win-x64/libz3.dll',
                                     package.RESOURCE_PREFIX + 'win-x64/z3java.dll'})
        for name in self.api_entries:
            self.assertEqual(entries[name], self.api_entries[name])
        provenance = json.loads(entries['META-INF/z3/provenance.json'])
        self.assertTrue(provenance['prototype'])
        self.assertEqual(provenance['release_commit'], 'a' * 40)

    def test_corrupt_download_rejected_before_output(self):
        (self.root / self.name).write_bytes(b'broken')
        with self.assertRaisesRegex(ValueError, 'checksum'):
            self.build()
        self.assertFalse((self.root / 'out').exists())

    def test_missing_jni_library(self):
        del self.entries[self.prefix + 'bin/z3java.dll']
        self.write_release()
        with self.assertRaisesRegex(ValueError, 'z3java.dll'):
            self.build()

    def test_missing_license(self):
        del self.entries[self.prefix + 'LICENSE.txt']
        self.write_release()
        with self.assertRaisesRegex(ValueError, 'LICENSE.txt'):
            self.build()

    def test_cpu_mismatch(self):
        self.entries[self.prefix + 'bin/z3java.dll'] = pe(0xaa64)
        self.write_release()
        with self.assertRaisesRegex(ValueError, 'architecture mismatch'):
            self.build()

    def test_source_provenance_mismatch(self):
        self.preparation['release_commit'] = 'b' * 40
        with self.assertRaisesRegex(ValueError, 'provenance'):
            self.build()

    def test_prepared_jar_modification(self):
        self.api = archive({**self.api_entries, 'unexpected.txt': b'changed'})
        with self.assertRaisesRegex(ValueError, 'provenance'):
            self.build()

    def test_wrong_asset_version(self):
        asset = self.lock['platforms']['win-x64']
        asset['name'] = 'z3-4.0.0-x64-win.zip'
        asset['url'] = 'https://github.com/Z3Prover/z3/releases/download/z3-5.3.2/' + asset['name']
        with self.assertRaisesRegex(ValueError, 'version mismatch'):
            self.build()

    def test_unexpected_origin(self):
        self.lock['platforms']['win-x64']['url'] = 'https://example.invalid/binary.zip'
        with self.assertRaisesRegex(ValueError, 'Unexpected release asset URL'):
            self.build()

    def test_duplicate_platform(self):
        with self.assertRaisesRegex(ValueError, 'duplicates'):
            self.build(platforms=['win-x64', 'win-x64'])

    def test_workflow_run_identity(self):
        expected = {'repository': 'example/z3', 'run_id': '123', 'run_attempt': '1',
                    'source_commit': 'a' * 40}
        self.lock['input_kind'] = 'workflow-artifact'
        self.preparation['workflow'] = expected
        asset = self.lock['platforms']['win-x64']
        asset['workflow'] = dict(expected)
        asset['url'] = 'https://github.com/example/z3/actions/runs/123'
        self.build('matching-run')
        for key, wrong in (('run_id', '456'), ('run_attempt', '2'), ('source_commit', 'b' * 40)):
            with self.subTest(key=key):
                asset['workflow'] = {**expected, key: wrong}
                with self.assertRaisesRegex(ValueError, 'Mixed workflow'):
                    self.build('mixed-run')

    def test_collect_rejects_mixed_receipts(self):
        expected = {'repository': 'example/z3', 'run_id': '123', 'run_attempt': '1',
                    'source_commit': 'a' * 40}
        receipt = {'classifier': 'win-x64', 'workflow': expected, 'version': '5.3.2',
                   'runtime_version': '5.3.2.0', 'name': self.name,
                   'sha256': self.lock['platforms']['win-x64']['sha256']}
        directory = self.root / 'downloaded/java-native-win-x64'
        directory.mkdir(parents=True)
        (directory / self.name).write_bytes((self.root / self.name).read_bytes())
        metadata = directory / 'receipt-win-x64.json'
        metadata.write_bytes(package.json_bytes(receipt))
        with mock.patch.object(workflow_inputs, 'source_version', return_value=('5.3.2', '5.3.2.0')):
            workflow_inputs.collect(directory.parent, self.root / 'collected', ['win-x64'], expected)
            for change in ({'workflow': {**expected, 'run_id': 'other'}},
                           {'workflow': {**expected, 'run_attempt': '2'}},
                           {'workflow': {**expected, 'source_commit': 'b' * 40}},
                           {'version': '5.0.0'}, {'classifier': 'linux-x64'}):
                metadata.write_bytes(package.json_bytes({**receipt, **change}))
                with self.subTest(change=change), self.assertRaisesRegex(ValueError, 'Mixed run'):
                    workflow_inputs.collect(directory.parent, self.root / 'rejected', ['win-x64'], expected)

    def test_stale_output_directory(self):
        self.build()
        with self.assertRaisesRegex(ValueError, 'empty'):
            self.build()

    def test_jar_constraints(self):
        cases = [
            ({**self.api_entries, package.RESOURCE_PREFIX + 'win-x64/libz3.dll': pe()}, 'already contains'),
            ({**self.api_entries, 'META-INF/OLD.SF': b'signature'}, 'signed API'),
            ({**self.api_entries, 'newer.class': b'\xca\xfe\xba\xbe\0\0\0\x3d'}, 'newer than Java 8'),
            ({k: v for k, v in self.api_entries.items() if k != package.LOADER_CLASS}, 'Missing required'),
        ]
        for entries, message in cases:
            with self.subTest(message=message), self.assertRaisesRegex(ValueError, message):
                package.validate_api(entries)

    def test_duplicate_and_unsafe_entries(self):
        for name in ('../escape', '/absolute', 'C:/absolute'):
            with self.subTest(name=name), self.assertRaisesRegex(ValueError, 'unsafe'):
                package.checked_zip(archive({name: b'data'}))
        # ZipInfo normalizes backslashes when writing on Windows; mutate both
        # stored filename fields to exercise a truly noncanonical input ZIP.
        malformed = archive({'bin/ambiguous': b'data'}).replace(b'bin/ambiguous', b'bin\\ambiguous')
        with self.assertRaisesRegex(ValueError, 'unsafe'):
            package.checked_zip(malformed)
        stream = io.BytesIO()
        with warnings.catch_warnings():
            warnings.simplefilter('ignore', UserWarning)
            with zipfile.ZipFile(stream, 'w') as jar:
                jar.writestr('same', b'first')
                jar.writestr('same', b'second')
        with self.assertRaisesRegex(ValueError, 'Duplicate'):
            package.checked_zip(stream.getvalue())

    def test_linux_and_macos_architecture_headers(self):
        for classifier, machine in (('linux-x64', 62), ('linux-arm64', 183)):
            data = bytearray(64)
            data[:6] = b'\x7fELF\x02\x01'
            struct.pack_into('<H', data, 18, machine)
            package.validate_binary(data, classifier)
            struct.pack_into('<H', data, 18, 8)
            with self.assertRaisesRegex(ValueError, 'mismatch'):
                package.validate_binary(data, classifier)
        for classifier, machine in (('osx-x64', 0x1000007), ('osx-arm64', 0x100000c)):
            data = b'\xcf\xfa\xed\xfe' + struct.pack('<I', machine) + bytes(24)
            package.validate_binary(data, classifier)
        for data in (b'', b'\x7fELF', b'MZ', b'not a native library'):
            with self.subTest(data=data), self.assertRaises(ValueError):
                package.validate_binary(data, 'win-x64')


if __name__ == '__main__':
    unittest.main()
