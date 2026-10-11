############################################
# Copyright (c) 2026 Microsoft Corporation
#
# Dependency-free tests for the Lean checking helper.
############################################
import os
from pathlib import Path
import shutil
import subprocess
import tempfile
import unittest

_ROOT = Path(__file__).resolve().parents[2]
_SCRIPT = _ROOT / "scripts" / "check_lean.sh"
_BASH = shutil.which("bash")
_TOOLCHAIN = (_ROOT / "lean" / "lean-toolchain").read_text().strip()
_FAKE_ELAN = """#!/bin/bash
printf '%s\\0' "$@" >> "$ELAN_TEST_LOG"
printf '\\0' >> "$ELAN_TEST_LOG"
printf '%s\\n' "$PWD" >> "$ELAN_TEST_CWD"
if [[ "${4:-}" == "build" ]]; then
    exit "${ELAN_TEST_BUILD_STATUS:-0}"
fi
exit "${ELAN_TEST_LEAN_STATUS:-0}"
"""


@unittest.skipUnless(os.name == "posix" and _BASH, "requires Bash on POSIX")
class TestCheckLean(unittest.TestCase):
    def setUp(self):
        self.directory = tempfile.TemporaryDirectory()
        self.addCleanup(self.directory.cleanup)
        self.root = Path(self.directory.name).resolve()
        self.bin = self.root / "bin"
        self.bin.mkdir()
        self.elan = self.bin / "elan"
        self.elan.write_text(_FAKE_ELAN)
        self.elan.chmod(0o755)
        self.log = self.root / "calls"
        self.cwd_log = self.root / "directories"
        self.env = dict(os.environ)
        self.env.update({
            "PATH": str(self.bin) + os.pathsep + os.defpath,
            "HOME": str(self.root / "home"),
            "ELAN_TEST_LOG": str(self.log),
            "ELAN_TEST_CWD": str(self.cwd_log),
        })
        self.proof = self.root / "example proof.txt"
        self.proof.write_text("example : True := True.intro\n")

    def run_helper(self, *arguments):
        return subprocess.run(
            [_BASH, str(_SCRIPT), *arguments],
            cwd=self.root, env=self.env, text=True, capture_output=True, check=False,
        )

    def calls(self):
        if not self.log.exists():
            return []
        return [record.decode().split("\0")
                for record in self.log.read_bytes().split(b"\0\0") if record]

    def test_default_builds_the_pinned_project(self):
        result = self.run_helper()
        self.assertEqual(result.returncode, 0, result.stderr)
        self.assertEqual(self.calls(), [["run", _TOOLCHAIN, "lake", "build"]])
        self.assertEqual(self.cwd_log.read_text().splitlines(), [str(_ROOT / "lean")])
        self.assertIn("Lean checks passed.", result.stdout)

    def test_relative_paths_spaces_and_strict_flags(self):
        result = self.run_helper(self.proof.name)
        self.assertEqual(result.returncode, 0, result.stderr)
        self.assertEqual(self.calls(), [
            ["run", _TOOLCHAIN, "lake", "build"],
            ["run", _TOOLCHAIN, "lake", "env", "lean",
             "--trust=0", "-DwarningAsError=true", str(self.proof)],
        ])
        self.assertEqual(self.cwd_log.read_text().splitlines(), [str(_ROOT / "lean")] * 2)

    def test_absolute_paths_and_multiple_files(self):
        second = self.root / "second.lean"
        second.write_text("example : True := True.intro\n")
        result = self.run_helper("--", str(self.proof), str(second))
        self.assertEqual(result.returncode, 0, result.stderr)
        self.assertEqual([call[-1] for call in self.calls()[1:]], [str(self.proof), str(second)])

    def test_missing_file_is_rejected_before_building(self):
        result = self.run_helper("missing.lean")
        self.assertEqual(result.returncode, 2)
        self.assertIn("cannot read file", result.stderr)
        self.assertEqual(self.calls(), [])

    def test_directory_is_not_a_source_file(self):
        result = self.run_helper(str(self.root))
        self.assertEqual(result.returncode, 2)
        self.assertIn("cannot read file", result.stderr)
        self.assertEqual(self.calls(), [])

    def test_build_failure_stops_checking(self):
        self.env["ELAN_TEST_BUILD_STATUS"] = "7"
        result = self.run_helper(str(self.proof))
        self.assertEqual(result.returncode, 7)
        self.assertEqual(len(self.calls()), 1)
        self.assertNotIn("Lean checks passed.", result.stdout)

    def test_lean_failure_is_preserved_and_stops_later_files(self):
        self.env["ELAN_TEST_LEAN_STATUS"] = "9"
        result = self.run_helper(str(self.proof), str(self.proof))
        self.assertEqual(result.returncode, 9)
        self.assertEqual(len(self.calls()), 2)
        self.assertNotIn("Lean checks passed.", result.stdout)

    def test_missing_elan_has_an_actionable_error(self):
        self.env["PATH"] = os.defpath
        result = self.run_helper()
        self.assertEqual(result.returncode, 127)
        self.assertIn("elan was not found", result.stderr)
        self.assertEqual(self.calls(), [])

    def test_standard_elan_home_is_a_fallback(self):
        fallback = Path(self.env["HOME"]) / ".elan" / "bin" / "elan"
        fallback.parent.mkdir(parents=True)
        shutil.copyfile(self.elan, fallback)
        fallback.chmod(0o755)
        self.env["PATH"] = os.defpath
        result = self.run_helper(str(self.proof))
        self.assertEqual(result.returncode, 0, result.stderr)
        self.assertEqual(len(self.calls()), 2)

    def test_help_does_not_need_elan(self):
        self.env["PATH"] = os.defpath
        result = self.run_helper("--help")
        self.assertEqual(result.returncode, 0)
        self.assertIn("Usage:", result.stdout)
        self.assertEqual(self.calls(), [])


if __name__ == "__main__":
    unittest.main()
