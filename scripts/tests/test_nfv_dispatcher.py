############################################
# Copyright (c) 2026 Microsoft Corporation
#
# Regression tests for advisory NFV dispatch reporting.
############################################
import os
from pathlib import Path
import shutil
import subprocess
import tempfile
import textwrap
import unittest


WORKFLOW = (
    Path(__file__).resolve().parents[2]
    / ".github/workflows/nfv-formal-audit-dispatcher.yml"
)


class TestNFVDispatcher(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.workflow = WORKFLOW.read_text(encoding="utf-8")

    def step(self, name):
        return self.workflow.split(
            "      - name: " + name + "\n", 1
        )[1].split("\n      - name:", 1)[0]

    def test_failures_are_advisory_but_dispatch_requires_a_token(self):
        token = self.step("Generate GitHub App token")
        dispatch = self.step("Dispatch NFV audit")
        self.assertIn("continue-on-error: true", token)
        self.assertIn("continue-on-error: true", dispatch)
        self.assertIn("if: steps.app-token.outcome == 'success'", dispatch)
        self.assertIn("repositories: bench", token)

    def test_report_uses_original_outcomes_and_respects_cancellation(self):
        report = self.step("Report NFV dispatch status")
        self.assertIn("if: ${{ !cancelled() }}", report)
        self.assertIn("TOKEN_OUTCOME: ${{ steps.app-token.outcome }}", report)
        self.assertIn("DISPATCH_OUTCOME: ${{ steps.dispatch.outcome }}", report)
        self.assertNotIn("continue-on-error:", report)

    @unittest.skipUnless(shutil.which("bash"), "The workflow uses Bash")
    def run_report(self, token_outcome, dispatch_outcome):
        report = self.step("Report NFV dispatch status")
        script = textwrap.dedent(report.split("        run: |\n", 1)[1])
        with tempfile.TemporaryDirectory() as directory:
            summary = Path(directory) / "summary.md"
            env = os.environ.copy()
            env.update(
                TOKEN_OUTCOME=token_outcome,
                DISPATCH_OUTCOME=dispatch_outcome,
                GITHUB_STEP_SUMMARY=str(summary),
            )
            result = subprocess.run(
                ["bash", "--noprofile", "--norc", "-e", "-o", "pipefail", "-c", script],
                env=env,
                text=True,
                capture_output=True,
                check=False,
            )
            self.assertEqual(result.returncode, 0, result.stderr)
            text = summary.read_text(encoding="utf-8")
            self.assertIn("NFV audit (advisory)", text)
            self.assertIn("not whether it passed", text)
            self.assertIn("https://github.com/Z3Prover/bench/actions/workflows/", text)
            return result.stdout, text

    def test_token_failure_warns_and_reports_audit_not_run(self):
        output, summary = self.run_report("failure", "skipped")
        self.assertIn("::warning::NFV audit not run:", output)
        self.assertIn("token creation failed", summary)
        self.assertNotIn("NFV audit requested", summary)

    def test_dispatch_failure_warns_and_reports_audit_not_run(self):
        output, summary = self.run_report("success", "failure")
        self.assertIn("::warning::NFV audit not run:", output)
        self.assertIn("workflow dispatch failed", summary)
        self.assertNotIn("NFV audit requested", summary)

    def test_skipped_dispatch_is_not_reported_as_requested(self):
        output, summary = self.run_report("success", "skipped")
        self.assertIn("::warning::NFV audit not run:", output)
        self.assertIn("was skipped", summary)
        self.assertNotIn("NFV audit requested", summary)

    def test_success_reports_a_request_not_an_audit_verdict(self):
        output, summary = self.run_report("success", "success")
        self.assertNotIn("::warning::", output)
        self.assertIn("NFV audit requested", summary)
        self.assertNotIn("NFV audit not run", summary)


if __name__ == "__main__":
    unittest.main()
