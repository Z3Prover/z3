"""Selection-contract tests for the checker-only and full build scopes.

The dependency closures below are fixtures standing in for F*'s `--dep full`
output; these tests prove selection and wiring, not an end-to-end build.
"""

import json
import os
from pathlib import Path
import shutil
import subprocess
import tempfile
import unittest

import checker_scope


ROOT = Path(__file__).resolve().parents[1]
MANIFEST = json.loads((ROOT / "tools/checker_modules.json").read_text(encoding="utf-8"))
KERNEL = ["Z3CoreModel.fst", "Z3TypedQuantifier.fst", "Z3GhostStandardModel.fst",
          "Z3CoreKernel.fst", "Z3QuantifierKernel.fst", "Z3BinderKernel.fst"]


def closure(*extra, without=KERNEL):
    return {m for m in MANIFEST["modules"] + MANIFEST["cherry_modules"] if m not in without} | set(extra)


PWSH = os.environ.get("PWSH") or shutil.which("pwsh")
FAKE_FSTAR = """#!/bin/sh
printf '%s\\n' "$*" >> "$FAKE_FSTAR_LOG"
case " $* " in
  *" --version "*) echo "F* fake" ;;
  *" --dep "*) cat "$FAKE_DEP_OUTPUT" ;;
  *" --cache_checked_modules "*)
    previous=; cache=; module=
    for arg in "$@"; do
      [ "$previous" = --cache_dir ] && cache=$arg
      previous=$arg; module=$arg
    done
    touch "$cache/$(basename "$module").checked" ;;
esac
"""


def dep_output(directory, files, interfaces):
    lines = ["Z3List.fst.checked: \\", "\tZ3List.fst", "", "ALL_FST_FILES= \\"]
    lines += [f"\t{name} \\" for name in files[:-1]] + [f"\t{files[-1]}", "", "ALL_FSTI_FILES= \\"]
    lines += [f"\t{name} \\" for name in interfaces[:-1]] + [f"\t{interfaces[-1]}", ""]
    lines += ["ALL_CHECKED_FILES= \\", f"\t{directory / 'Z3Unlisted.fst.checked'}", ""]
    return "\n".join(lines)


class DependencyOutputTests(unittest.TestCase):
    def test_reads_only_this_directorys_sources_from_the_file_lists(self):
        output = dep_output(
            ROOT,
            ["/opt/fstar/lib/fstar/ulib/FStar.List.Tot.Base.fst", "Z3List.fst",
             str(ROOT / "Z3NativeProof.fst"), str(ROOT / "audits/Z3Elsewhere.fst")],
            ["/opt/fstar/lib/fstar/ulib/FStar.All.fsti", "Z3Native.fsti"],
        )
        self.assertEqual(checker_scope.dependency_files(output, ROOT),
                         {"Z3List.fst", "Z3NativeProof.fst", "Z3Native.fsti"})

    def test_crlf_output_is_accepted(self):
        output = dep_output(ROOT, ["Z3List.fst", "Z3AstTheory.fst"], ["Z3Native.fsti"])
        self.assertEqual(checker_scope.dependency_files(output.replace("\n", "\r\n"), ROOT),
                         {"Z3List.fst", "Z3AstTheory.fst", "Z3Native.fsti"})

    def test_output_without_file_lists_is_an_error(self):
        with self.assertRaisesRegex(RuntimeError, "ALL_FST_FILES"):
            checker_scope.dependency_files("Z3List.fst.checked: \\\n\tZ3List.fst\n", ROOT)


class SelectionTests(unittest.TestCase):
    roots = ["Z3SortedProof.fst", "Z3Native.fsti", "Z3NativeProof.fst"]

    def test_checker_scope_verifies_the_production_closure_in_manifest_order(self):
        modules, tests = checker_scope.select(MANIFEST, "ocaml", False, closure(), self.roots)
        self.assertEqual(modules, [m for m in MANIFEST["modules"] if m not in KERNEL])
        self.assertEqual(tests, [])
        self.assertIn("Z3SortedRealExtension.fst", modules)
        self.assertNotIn("Z3IdTable-c.cherry.fst", modules)

    def test_full_scope_verifies_every_registered_module_and_test(self):
        modules, tests = checker_scope.select(MANIFEST, "ocaml", True, closure(), self.roots)
        self.assertEqual(modules, MANIFEST["modules"])
        self.assertEqual(tests, MANIFEST["tests"])

    def test_cherry_scopes_add_the_cherry_overrides_root_and_tests(self):
        cherry = closure("Z3Cherry.fst", without=KERNEL + ["Z3BvFreshModel.fst"])
        modules, tests = checker_scope.select(MANIFEST, "cherry", False, cherry, ["Z3Cherry.fst"])
        self.assertEqual(modules, [m for m in MANIFEST["modules"] if m in cherry]
                         + MANIFEST["cherry_modules"] + ["Z3Cherry.fst"])
        self.assertEqual(tests, [])
        modules, tests = checker_scope.select(MANIFEST, "cherry", True, cherry, ["Z3Cherry.fst"])
        self.assertEqual(modules, MANIFEST["modules"] + MANIFEST["cherry_modules"] + ["Z3Cherry.fst"])
        self.assertEqual(tests, MANIFEST["tests"] + ["Z3CherryTests.fst"])

    def test_a_test_module_in_the_checker_closure_fails_both_scopes(self):
        for full in (False, True):
            with self.subTest(full=full), self.assertRaisesRegex(RuntimeError, "Z3RealPower.fst"):
                checker_scope.select(MANIFEST, "ocaml", full, closure("Z3RealPower.fst"), self.roots)

    def test_an_unregistered_dependency_fails(self):
        with self.assertRaisesRegex(RuntimeError, "Z3Unregistered.fst"):
            checker_scope.select(MANIFEST, "ocaml", False, closure("Z3Unregistered.fst"), self.roots)

    def test_a_root_outside_the_closure_fails(self):
        with self.assertRaisesRegex(RuntimeError, "Z3SortedProof.fst"):
            checker_scope.select(MANIFEST, "ocaml", False,
                                 closure(without=KERNEL + ["Z3SortedProof.fst"]), self.roots)

    def test_checker_extraction_entries_are_the_closure_implementations(self):
        entries = checker_scope.extraction_entries(MANIFEST, closure(), False)
        self.assertEqual(entries, [m for m in MANIFEST["modules"]
                                   if m not in KERNEL and not m.endswith(".fsti")])
        self.assertNotIn("Z3Native.fsti", entries)

    def test_full_extraction_entries_are_every_registered_implementation(self):
        entries = checker_scope.extraction_entries(MANIFEST, closure(), True)
        self.assertEqual(entries, [m for m in MANIFEST["modules"] if not m.endswith(".fsti")])
        self.assertEqual(len(entries), 89)
        self.assertTrue(set(KERNEL) <= set(entries))


@unittest.skipUnless(os.name == "posix" and PWSH and shutil.which("git"),
                     "needs PowerShell and git on a POSIX host")
class PowerShellWiringTests(unittest.TestCase):
    """Run build_ocaml_checker.ps1 against fake cmake, z3, F* and bash executables."""

    def build(self, *flags):
        temporary = Path(tempfile.mkdtemp(prefix="checker-scope-"))
        self.addCleanup(shutil.rmtree, temporary)
        fstar = temporary / "fstar"
        shutil.copytree(ROOT / "ocaml_runtime", fstar / "ocaml_runtime")
        (fstar / "tools").mkdir()
        for name in ("build_ocaml_checker.ps1", "checker_scope.py", "checker_modules.json"):
            shutil.copy(ROOT / "tools" / name, fstar / "tools" / name)
        for module in MANIFEST["modules"] + MANIFEST["cherry_modules"] + MANIFEST["tests"]:
            (fstar / module).touch()
        subprocess.run(["git", "init", "-q"], cwd=temporary, check=True)
        subprocess.run(["git", "-c", "user.name=test", "-c", "user.email=test@example.com",
                        "commit", "-q", "--allow-empty", "-m", "fixture"], cwd=temporary, check=True)
        bin_dir = temporary / "bin"
        executables = {
            bin_dir / "cmake": "#!/bin/sh\n",
            bin_dir / "bash": '#!/bin/sh\ncp "$1" "$FAKE_NATIVE_SCRIPT"\n',
            bin_dir / "fstar.exe": FAKE_FSTAR,
            temporary / "install/bin/z3": "#!/bin/sh\necho 'Z3 version 5.4.0 - 64 bit'\n",
        }
        for path, text in executables.items():
            path.parent.mkdir(parents=True, exist_ok=True)
            path.write_text(text, encoding="utf-8")
            path.chmod(0o755)
        names = sorted(closure())
        (temporary / "dep.txt").write_text(dep_output(
            fstar, [n for n in names if n.endswith(".fst")], [n for n in names if n.endswith(".fsti")]))
        environment = dict(os.environ, PATH=f"{bin_dir}{os.pathsep}{os.environ['PATH']}",
                           FAKE_FSTAR_LOG=str(temporary / "fstar.log"),
                           FAKE_DEP_OUTPUT=str(temporary / "dep.txt"),
                           FAKE_NATIVE_SCRIPT=str(temporary / "native.sh"))
        result = subprocess.run(
            [PWSH, "-NoProfile", "-File", fstar / "tools/build_ocaml_checker.ps1",
             "-FstarExe", bin_dir / "fstar.exe", "-Z3WindowsBuildDir", temporary / "z3-build",
             "-Z3InstallDir", temporary / "install", "-CacheDir", temporary / "cache",
             "-WslBuildDir", temporary / "native", "-ReportDir", temporary / "report",
             "-BuildCherry", "-CherryFstarExe", bin_dir / "fstar.exe", *flags],
            env=environment, capture_output=True, text=True, timeout=300)
        verified, entries = [], None
        self.assertTrue((temporary / "fstar.log").is_file(), result.stdout + result.stderr)
        for line in (temporary / "fstar.log").read_text(encoding="utf-8").splitlines():
            parts = line.split()
            if "--cache_checked_modules" in parts:
                verified.append(parts[-1])
            if "--codegen" in parts:
                entries = [parts[i + 1] for i, part in enumerate(parts) if part == "--custard_entry_module"]
        native = (temporary / "native.sh").read_text(encoding="utf-8")
        report = json.loads((temporary / "report/scope-ocaml.json").read_text(encoding="utf-8"))
        return result, verified, entries, native, report

    def test_without_run_tests_only_the_closure_is_verified_and_no_tests_are_built(self):
        result, verified, entries, native, report = self.build()
        self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
        self.assertEqual(verified, [m for m in MANIFEST["modules"] if m not in KERNEL])
        self.assertEqual(entries, [m[:-4] for m in MANIFEST["modules"]
                                   if m not in KERNEL and m.endswith(".fst")])
        self.assertNotIn("--run-tests", native)
        self.assertNotIn("native-tests", native)
        self.assertIn("/report/scope-cherry.json", native)
        self.assertEqual((report["mode"], report["native_tests"]), ("checker", False))
        self.assertEqual(report["selected_modules"], verified)
        self.assertEqual(sorted(report["registered_not_selected"]),
                         sorted(KERNEL + MANIFEST["tests"]))

    def test_run_tests_verifies_every_module_and_test_then_runs_native_tests(self):
        result, verified, entries, native, report = self.build("-RunTests")
        self.assertNotEqual(result.returncode, 0)
        self.assertIn("Native checker CLI tests failed", result.stdout + result.stderr)
        self.assertEqual(verified, MANIFEST["modules"] + MANIFEST["tests"])
        self.assertEqual(entries, [m[:-4] for m in MANIFEST["modules"] if m.endswith(".fst")])
        self.assertIn("--run-tests", native)
        self.assertIn("native-tests", native)
        self.assertEqual((report["mode"], report["registered_not_selected"]), ("full", []))


if __name__ == "__main__":
    unittest.main()
