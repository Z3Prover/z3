"""Build-manifest and Cherry foreign-interface generator regressions."""

import argparse
import hashlib
import json
from pathlib import Path
import subprocess
import tarfile
import tempfile
import unittest
from unittest.mock import patch

from build_cherry_checker import failure_stubs
import package_checker


class CherryBuildTests(unittest.TestCase):
    def test_failure_stubs_preserve_each_monomorphic_return_type(self):
        generated = (
            "extern Z3AstTheory_expr Z3Native_fail__expr(cherry_string);\n"
            "extern cherry_int Z3Native_fail__int(cherry_string);\n"
            "extern cherry_int Z3Native_fail__int(cherry_string);\n"
            "extern cherry_int Z3Native_ast_id(Z3_ast);\n"
        )
        stubs = failure_stubs(generated)
        self.assertIn('extern "C" Z3AstTheory_expr Z3Native_fail__expr', stubs)
        self.assertIn('extern "C" cherry_int Z3Native_fail__int', stubs)
        self.assertEqual(stubs.count("checker::fail(message);"), 2)
        self.assertNotIn("Z3Native_ast_id", stubs)

    def test_missing_failure_interface_is_an_explicit_error(self):
        with self.assertRaisesRegex(RuntimeError, "native failure interface"):
            failure_stubs("")

    def test_shared_module_manifest_is_complete_and_dependency_ordered(self):
        root = Path(__file__).resolve().parents[1]
        manifest = json.loads((root / "tools/checker_modules.json").read_text(encoding="utf-8"))
        modules = manifest["modules"] + manifest["tests"]
        self.assertEqual(len(modules), len(set(modules)))
        for module in modules:
            with self.subTest(module=module):
                self.assertTrue((root / module).is_file())
        self.assertLess(modules.index("Z3ProofDocument.fst"), modules.index("Z3NativeProof.fst"))
        self.assertLess(modules.index("Z3SortedProof.fst"), modules.index("Z3NativeProof.fst"))
        self.assertEqual(manifest["modules"][-3:],
                         ["Z3Native.fsti", "Z3NativeProof.fst", "Z3Tptp.fst"])


class CheckerPackageTests(unittest.TestCase):
    def prepare(self, root):
        checker = root / "checker"
        checker.write_bytes(b"\x7fELFtest-executable")
        fstar = root / "fstar/bin/fstar.exe"
        fstar.parent.mkdir(parents=True)
        (root / "LICENSE.txt").write_text("Z3 license", encoding="ascii")
        (fstar.parent.parent / "LICENSE").write_text("F* license", encoding="ascii")
        return argparse.Namespace(checker=checker, fstar=fstar, backend="cherry",
                                  output_dir=root / "artifacts", extra_license=[])

    def test_archive_preserves_permissions_metadata_licenses_and_clean_environment(self):
        with tempfile.TemporaryDirectory() as temporary:
            root = Path(temporary)
            args = self.prepare(root)
            with patch.object(package_checker, "ROOT", root), \
                 patch.object(package_checker.platform, "machine", return_value="x86_64"), \
                 patch.object(package_checker.platform, "platform", return_value="Linux-test"), \
                 patch.object(package_checker.subprocess, "check_output",
                              side_effect=["commit\n", "F* nightly\n", "libc.so.6 => /lib/libc.so.6\n"]), \
                 patch.object(package_checker.subprocess, "run",
                              return_value=subprocess.CompletedProcess([], 0, "ACCEPT\n", "")) as smoke:
                package_checker.package(args)
            archive = args.output_dir / "pulse-checker-cherry-linux-x86_64.tar.gz"
            digest = hashlib.sha256(archive.read_bytes()).hexdigest()
            self.assertEqual(archive.with_suffix(".gz.sha256").read_text(encoding="ascii"),
                             f"{digest}  {archive.name}\n")
            with tarfile.open(archive) as tar:
                prefix = "pulse-checker-cherry-linux-x86_64/"
                self.assertEqual(tar.getmember(prefix + "checker").mode, 0o755)
                self.assertEqual(tar.extractfile(prefix + "LICENSE-0-LICENSE.txt").read(), b"Z3 license")
                metadata = json.load(tar.extractfile(prefix + "build.json"))
                self.assertEqual(metadata["commit"], "commit")
                self.assertEqual(metadata["sha256"], hashlib.sha256(args.checker.read_bytes()).hexdigest())
            self.assertEqual(smoke.call_args.kwargs["env"], {"PATH": "/usr/bin:/bin", "LC_ALL": "C.UTF-8"})

    def test_missing_shared_library_rejects_packaging(self):
        with tempfile.TemporaryDirectory() as temporary:
            root = Path(temporary)
            args = self.prepare(root)
            with patch.object(package_checker, "ROOT", root), \
                 patch.object(package_checker.platform, "platform", return_value="Linux-test"), \
                 patch.object(package_checker.subprocess, "check_output",
                              side_effect=["commit\n", "F* nightly\n", "libz3.so => not found\n"]):
                with self.assertRaisesRegex(RuntimeError, "unresolved shared libraries"):
                    package_checker.package(args)
            self.assertEqual(list(args.output_dir.glob("*.tar.gz")), [])

    def test_failed_clean_environment_smoke_rejects_packaging(self):
        with tempfile.TemporaryDirectory() as temporary:
            root = Path(temporary)
            args = self.prepare(root)
            with patch.object(package_checker, "ROOT", root), \
                 patch.object(package_checker.platform, "platform", return_value="Linux-test"), \
                 patch.object(package_checker.subprocess, "check_output",
                              side_effect=["commit\n", "F* nightly\n", "libc.so.6 => /lib/libc.so.6\n"]), \
                 patch.object(package_checker.subprocess, "run",
                              return_value=subprocess.CompletedProcess([], 2, "", "ERROR")):
                with self.assertRaisesRegex(RuntimeError, "clean-environment smoke"):
                    package_checker.package(args)
            self.assertEqual(list(args.output_dir.glob("*.tar.gz")), [])


if __name__ == "__main__":
    unittest.main()
