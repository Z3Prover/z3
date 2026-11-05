"""Build-manifest and Cherry foreign-interface generator regressions."""

import argparse
import hashlib
import json
from pathlib import Path
import shutil
import subprocess
import tarfile
import tempfile
import unittest
from unittest.mock import patch

import build_cherry_checker
from build_cherry_checker import failure_stubs
import package_checker


MANIFEST = json.loads((Path(__file__).resolve().parents[1] / "tools/checker_modules.json")
                      .read_text(encoding="utf-8"))
KERNEL = ["Z3CoreModel.fst", "Z3TypedQuantifier.fst", "Z3GhostStandardModel.fst",
          "Z3CoreKernel.fst", "Z3QuantifierKernel.fst", "Z3BinderKernel.fst"]


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
        modules = manifest["modules"] + manifest["cherry_modules"] + manifest["tests"]
        self.assertEqual(len(modules), len(set(modules)))
        for module in modules:
            with self.subTest(module=module):
                self.assertTrue((root / module).is_file())
        self.assertLess(modules.index("Z3ProofDocument.fst"), modules.index("Z3NativeProof.fst"))
        self.assertLess(modules.index("Z3SortedProof.fst"), modules.index("Z3NativeProof.fst"))
        self.assertEqual(manifest["modules"][-2:], ["Z3Native.fsti", "Z3NativeProof.fst"])


class CherryScopeWiringTests(unittest.TestCase):
    """Drive build() with recorded commands and a fixture dependency closure, not real tools."""

    def build(self, run_tests):
        temporary = Path(tempfile.mkdtemp(prefix="cherry-scope-"))
        self.addCleanup(shutil.rmtree, temporary)
        for path in ("install/bin/z3", "install/lib/libz3.a", "fstar/ulib/c/cherry.c"):
            (temporary / path).parent.mkdir(parents=True, exist_ok=True)
            (temporary / path).touch()
        output = temporary / "build"
        commands = []

        def run(command, **kwargs):
            command = [str(arg) for arg in command]
            commands.append(command)
            stdout = {"-version": "Z3 version 5.4.0 - 64 bit", "-dumpfullversion": "15.2.0",
                      "--locate_lib": str(temporary / "fstar")}.get(command[-1], "tool 15.2.0")
            if "--codegen" in command:
                (output / "generated/Z3Cherry.c").write_text(
                    "extern cherry_int Z3Native_fail__int(cherry_string);\n", encoding="utf-8")
            elif "-o" in command:
                Path(command[command.index("-o") + 1]).write_bytes(b"binary")
            return subprocess.CompletedProcess(command, 0, stdout, "")

        closure = ({m for m in MANIFEST["modules"] + MANIFEST["cherry_modules"] if m not in KERNEL}
                   | {"Z3Cherry.fst"})
        args = argparse.Namespace(
            fstar=temporary / "fstar/bin/fstar.exe", z3_install=temporary / "install",
            build_dir=output, cache_dir=None, cc="gcc-15", cxx="g++-15",
            run_tests=run_tests, sanitize=False, report=temporary / "scope-cherry.json")
        with patch.object(build_cherry_checker, "run", side_effect=run), \
             patch.object(build_cherry_checker.checker_scope, "dependency_closure",
                          return_value=closure) as dependencies, \
             patch.object(build_cherry_checker.checker_scope.subprocess, "check_output",
                          return_value="source\n"), \
             patch.object(build_cherry_checker.platform, "system", return_value="Linux"), \
             patch.object(build_cherry_checker.platform, "machine", return_value="x86_64"):
            build_cherry_checker.build(args)
        self.assertIn("--dep", dependencies.call_args.args[0])
        self.assertEqual(Path(dependencies.call_args.args[0][-1]).name, "Z3Cherry.fst")
        verified = [Path(c[-1]).name for c in commands if "--cache_checked_modules" in c]
        extraction = next(c for c in commands if "--codegen" in c)
        metadata = json.loads((output / "build.json").read_text(encoding="utf-8"))
        report = json.loads(args.report.read_text(encoding="utf-8"))
        self.assertEqual((report["source_sha"], report["backend"]), ("source", "cherry"))
        return commands, verified, extraction, metadata, report

    def test_checker_scope_verifies_the_closure_and_builds_no_tests(self):
        commands, verified, extraction, metadata, report = self.build(False)
        self.assertEqual(verified, [m for m in MANIFEST["modules"] if m not in KERNEL]
                         + MANIFEST["cherry_modules"] + ["Z3Cherry.fst"])
        self.assertEqual(Path(extraction[-1]).name, "Z3Cherry.fst")
        self.assertNotIn("Z3CherryTests.run", extraction)
        self.assertFalse(any(c[-1].endswith("checker-tests") for c in commands))
        self.assertFalse(any("test_native_checker.py" in " ".join(c) for c in commands))
        self.assertEqual((metadata["mode"], metadata["verified_modules"]), ("checker", len(verified)))
        self.assertEqual((report["mode"], report["selected_modules"]), ("checker", verified))

    def test_run_tests_verifies_every_module_and_test_then_runs_both_suites(self):
        commands, verified, extraction, metadata, report = self.build(True)
        self.assertEqual(verified, MANIFEST["modules"] + MANIFEST["cherry_modules"] + ["Z3Cherry.fst"]
                         + MANIFEST["tests"] + ["Z3CherryTests.fst"])
        self.assertEqual(Path(extraction[-1]).name, "Z3CherryTests.fst")
        self.assertIn("Z3CherryTests.run", extraction)
        self.assertTrue(any(c[-1].endswith("checker-tests") for c in commands))
        self.assertTrue(any("test_native_checker.py" in " ".join(c) for c in commands))
        self.assertEqual((metadata["mode"], report["registered_not_selected"]), ("full", []))


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
