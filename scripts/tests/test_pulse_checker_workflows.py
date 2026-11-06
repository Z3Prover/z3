############################################
# Copyright (c) 2026 Microsoft Corporation
#
# Structure tests for the checker-only and full Pulse checker workflows.
############################################
from pathlib import Path
import re
import unittest


_REPO_ROOT = Path(__file__).resolve().parents[2]
_WORKFLOWS = _REPO_ROOT / ".github/workflows"
_INSTALL = ".github/scripts/install-pulse-checker-toolchains.sh"
_NIGHTLY_GUARD = """\
      github.event_name != 'workflow_run' ||
      (github.event.workflow_run.conclusion == 'success' &&
       github.event.workflow_run.path == '.github/workflows/nightly.yml' &&
       github.event.workflow_run.head_repository.full_name == github.repository &&
       github.event.workflow_run.head_branch == github.event.repository.default_branch &&
       (github.event.workflow_run.event == 'schedule' ||
        github.event.workflow_run.event == 'workflow_dispatch'))
"""


def _read(name):
    return (_WORKFLOWS / name).read_text(encoding="utf-8")


def _jobs(workflow):
    body = workflow.split("\njobs:\n", 1)[1]
    names = re.findall(r"^  ([A-Za-z0-9_-]+):\n", body, re.MULTILINE)
    blocks = re.split(r"^  [A-Za-z0-9_-]+:\n", body, flags=re.MULTILINE)[1:]
    return dict(zip(names, blocks))


def _top(workflow, key):
    return workflow.split(f"\n{key}:\n", 1)[1].split("\n\n", 1)[0]


def _env_pins(job):
    return re.findall(r"^      ((?:CHERRY_)?FSTAR_(?:VERSION|SHA256)|OPAM_SWITCH): (.+)$", job, re.MULTILINE)


def _build_command(job):
    return job.split("pwsh -NoProfile -File fstar/tools/build_ocaml_checker.ps1", 1)[1].split("2>&1", 1)[0]


class TestPulseCheckerWorkflows(unittest.TestCase):
    def setUp(self):
        self.build = _read("pulse-checker-build.yml")
        self.full = _read("pulse-checker-full.yml")

    def test_two_independent_workflows_with_stable_names(self):
        self.assertTrue(self.build.startswith("name: Build Pulse native checkers\n"))
        self.assertTrue(self.full.startswith("name: Verify all Pulse checker files\n"))
        self.assertEqual(list(_jobs(self.build)), ["build", "publish-nightly"])
        self.assertEqual(list(_jobs(self.full)), ["verify"])
        self.assertNotIn("needs:", self.full)
        self.assertNotIn("needs:", _jobs(self.build)["build"])
        self.assertNotIn("pulse-checker-full", self.build)
        self.assertNotEqual(_top(self.build, "concurrency"), _top(self.full, "concurrency"))

    def test_checker_only_build_verifies_without_tests_and_full_runs_every_test(self):
        checker = _build_command(_jobs(self.build)["build"])
        full = _build_command(_jobs(self.full)["verify"])
        self.assertNotIn("-RunTests", checker)
        self.assertIn("-BuildCherry", checker)
        self.assertIn("-RunTests -BuildCherry", full)
        for command in (checker, full):
            self.assertIn('-ReportDir "$REPORT_DIR"', command)
        self.assertIn('"mode":"checker"', _jobs(self.build)["build"])
        self.assertIn('"mode":"full"', _jobs(self.full)["verify"])

    def test_only_the_checker_build_packages_uploads_and_publishes_binaries(self):
        build = _jobs(self.build)["build"]
        for backend in ("ocaml", "cherry"):
            self.assertIn(f"--backend {backend}", build)
            self.assertIn(f"name: pulse-checker-{backend}-linux-x86_64", build)
        self.assertIn("name: pulse-checker-build-report", build)
        verify = _jobs(self.full)["verify"]
        self.assertNotIn("package_checker.py", verify)
        self.assertEqual(re.findall(r"^          name: (.+)$", verify, re.MULTILINE),
                         ["pulse-checker-full-report"])
        upload = verify.split("name: pulse-checker-full-report", 1)[0].rsplit("- name:", 1)[1]
        self.assertIn("if: always()", upload)
        self.assertNotIn("contents: write", self.full)
        self.assertNotIn("publish", self.full)

    def test_publisher_is_unchanged_and_the_only_writer(self):
        publish = _jobs(self.build)["publish-nightly"]
        self.assertIn("needs: build", publish)
        self.assertIn("if: ${{ github.event_name == 'workflow_run' }}", publish)
        self.assertIn("contents: write", publish)
        self.assertIn("group: nightly-release", publish)
        self.assertIn("ref: ${{ github.workflow_sha }}", publish)
        self.assertEqual(self.build.count("contents: write"), 1)

    def test_shared_triggers_guards_pins_and_read_only_checkouts(self):
        build, verify = _jobs(self.build)["build"], _jobs(self.full)["verify"]
        for workflow, name, job in ((self.build, "pulse-checker-build.yml", build),
                                    (self.full, "pulse-checker-full.yml", verify)):
            with self.subTest(workflow=name):
                self.assertEqual(_top(workflow, "permissions"), "  contents: read")
                self.assertIn("    workflows: [Nightly Build]\n    types: [completed]\n", workflow)
                self.assertIn("  workflow_dispatch:\n", workflow)
                triggers = _top(workflow, "on")
                for event in ("push", "pull_request"):
                    paths = re.split(r"\n  (?=\S)", triggers.split(f"  {event}:\n", 1)[1], maxsplit=1)[0]
                    for path in ("fstar/**", f".github/workflows/{name}", _INSTALL):
                        self.assertIn(f"- '{path}'", paths)
                self.assertIn(_NIGHTLY_GUARD, job)
                self.assertIn("ref: ${{ github.event.workflow_run.head_sha || "
                              "github.event.pull_request.head.sha || github.sha }}", job)
                self.assertIn("persist-credentials: false", job)
                self.assertNotIn("permissions:", job)
                self.assertIn(f"run: bash {_INSTALL}", job)
                for line in re.findall(r"uses: (\S+)", workflow):
                    self.assertRegex(line, r"@[0-9a-f]{40}$")
                self.assertNotIn("secrets.", workflow)
                self.assertNotIn("${{ inputs.", workflow)
        self.assertEqual(_env_pins(build), _env_pins(verify))
        self.assertEqual(len(_env_pins(build)), 5)

    def test_toolchain_script_checks_the_pinned_digests(self):
        script = (_REPO_ROOT / _INSTALL).read_text(encoding="utf-8")
        self.assertTrue(script.startswith("#!/usr/bin/env bash\nset -euo pipefail\n"))
        self.assertIn('printf \'%s  %s\\n\' "$FSTAR_SHA256" "$archive" | sha256sum --check', script)
        self.assertIn('printf \'%s  %s\\n\' "$CHERRY_FSTAR_SHA256" "$cherry_archive" | sha256sum --check',
                      script)
        self.assertNotRegex(script, r"[0-9a-f]{64}")

    def test_regressions_consume_only_checker_build_artifacts(self):
        regressions = _read("pulse-checker-regressions.yml")
        self.assertIn("    workflows: [Build Pulse native checkers]\n", regressions)
        self.assertIn("run.path.split('@')[0] !== '.github/workflows/pulse-checker-build.yml'",
                      regressions)
        self.assertNotIn("pulse-checker-full", regressions)
        self.assertNotIn("Verify all Pulse checker files", regressions)

    def test_repair_handles_failed_runs_of_both_workflows(self):
        producers = ["Pulse verification and native checker regressions",
                     "Build Pulse native checkers", "Verify all Pulse checker files"]
        source = _read("pulse-checker-repair.md")
        lock = _read("pulse-checker-repair.lock.yml")
        self.assertIn(f"    workflows: [{', '.join(producers)}]\n", source)
        self.assertIn("    workflows:\n" + "".join(f"      - {name}\n" for name in producers), lock)
        for repair in (source, lock):
            for path in ("pulse-checker-build.yml", "pulse-checker-full.yml"):
                self.assertIn(f"(github.event.workflow_run.path == '.github/workflows/{path}' &&", repair)
            self.assertEqual(repair.count("github.event.workflow_run.conclusion != 'success'"), 2)

if __name__ == "__main__":
    unittest.main()
