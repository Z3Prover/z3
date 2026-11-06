############################################
# Copyright (c) 2026 Microsoft Corporation
#
# Structure tests for the checker-only and full Pulse checker workflows.
############################################
from pathlib import Path
import json
import os
import re
import subprocess
import tempfile
import textwrap
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
                self.assertIn("ref: ${{ github.event.workflow_run.head_sha || github.sha }}", job)
                self.assertNotIn("github.event.pull_request.head.sha", job)
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

    def test_toolchain_install_avoids_recommended_system_ocaml_and_bounds_download_stalls(self):
        script = (_REPO_ROOT / _INSTALL).read_text(encoding="utf-8")
        installs = re.findall(r"sudo apt-get ([^\n]+)", script.replace("\\\n", " "))
        for command in installs:
            if "install" in command:
                self.assertIn("--no-install-recommends", command)
        packages = next(command for command in installs if "libgmp-dev" in command)
        for option in ("Acquire::Retries=3", "Acquire::http::Timeout=30", "Acquire::https::Timeout=30"):
            self.assertIn(option, packages)

    def test_source_metadata_accepts_only_the_triggering_pr_merge_or_original_commit(self):
        job = _jobs(_read("pulse-checker-regressions.yml"))["checker-build"]
        script = textwrap.dedent(job.rsplit("          script: |\n", 1)[1])
        harness = """\
const fs = require('node:fs');
const input = JSON.parse(fs.readFileSync(0, 'utf8'));
const AsyncFunction = Object.getPrototypeOf(async function() {}).constructor;
const github = {rest: {repos: {getCommit: async ({ref}) => {
  if (ref !== input.source) throw new Error('Unexpected source query');
  return {data: {parents: input.parents.map(sha => ({sha}))}};
}}}};
const core = {setOutput: (name, value) => console.log(JSON.stringify({[name]: value})),
  summary: {addRaw: () => ({write: async () => {}})}};
new AsyncFunction('github', 'context', 'core', input.script)(
  github, {repo: {owner: 'Z3Prover', repo: 'z3'}}, core
).catch(error => {console.error(error.message); process.exitCode = 1;});
"""
        head, base, merge = "a" * 40, "b" * 40, "c" * 40
        cases = [
            ("push", head, [], True),
            ("pull_request", head, [], True),
            ("pull_request", merge, [base, head], True),
            ("pull_request", merge, [head], False),
            ("pull_request", merge, [base, base], False),
            ("push", merge, [base, head], False),
            ("workflow_run", base, [], True),
        ]
        with tempfile.TemporaryDirectory() as directory:
            source_file = Path(directory) / "source.json"
            for event, source, parents, accepted in cases:
                with self.subTest(event=event, source=source, parents=parents):
                    source_file.write_text(json.dumps({"source_sha": source}), encoding="utf-8")
                    env = dict(os.environ, SOURCE_FILE=str(source_file),
                               RUN_HEAD_SHA=head, PRODUCER_EVENT=event)
                    result = subprocess.run(
                        ["node", "-e", harness], input=json.dumps({
                            "script": script, "source": source, "parents": parents
                        }).encode("utf-8"), env=env, capture_output=True)
                    self.assertEqual(result.returncode == 0, accepted, result.stderr.decode())
                    if accepted:
                        self.assertEqual(json.loads(result.stdout)["source_sha"], source)

    def test_fixed_qfbv_budget_matches_across_backends_and_fits_step_limits(self):
        workflow = _read("pulse-checker-regressions.yml")
        default = int(re.search(r"qfbv_total_timeout_seconds:\n.*?\n        default: (\d+)",
                                workflow, re.DOTALL).group(1))
        solver_timeout = int(re.search(r"solver_timeout_ms:\n.*?\n        default: (\d+)",
                                       workflow, re.DOTALL).group(1))
        self.assertGreaterEqual(default * 1000, 300 * solver_timeout)
        jobs = _jobs(workflow)
        ocaml = jobs["build-test-report"].split(
            "- name: Run native checker on 300 fixed QF_BV certificates", 1)[1].split(
                "\n      - name:", 1)[0]
        cherry = jobs["cherry-regressions"].split(
            "- name: Replay the proof corpus, identical SMT-LIB samples", 1)[1].split(
                "\n      - name:", 1)[0]
        self.assertIn(f'${{TOTAL_TIMEOUT_SECONDS:-{default}}}', ocaml)
        self.assertIn(f'${{QFBV_TIMEOUT_SECONDS:-{default}}}', cherry)
        self.assertIn("--expected-cases 300", ocaml)
        self.assertIn("count=300", cherry)
        self.assertGreater(int(re.search(r"timeout-minutes: (\d+)", ocaml).group(1)) * 60,
                           default)
        self.assertGreaterEqual(int(re.search(r"timeout-minutes: (\d+)",
                                             jobs["cherry-regressions"]).group(1)),
                                int(re.search(r"timeout-minutes: (\d+)", cherry).group(1)) + 80)

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
