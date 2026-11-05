############################################
# Copyright (c) 2026 Microsoft Corporation
#
# Dependency-free tests for the Markdown summary of scripts/ci_lean_proofs.sh.
############################################
import json
from pathlib import Path
import subprocess
import sys
import tempfile
import unittest

_ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(_ROOT / "scripts"))
import lean_proof_summary  # noqa: E402

_UNITTEST_LOG = """\
test_a (test_proof_to_lean_uf.TestUF.test_a) ... ok
test_b (test_proof_to_lean_uf.TestUF.test_b)
Docstring on its own line. ... ok
test_c (test_proof_to_lean_lia.TestLIA.test_c) ... skipped 'requires the pinned Lean toolchain'
test_d (test_proof_to_lean_lia.TestLIA.test_d) ... FAIL
test_e (test_proof_to_lean_lia.TestLIA.test_e) ... ERROR
input.smt2   logic_unknown smt-clause-log-nopp  lean-verified   0.00s
test_f (test_proof_to_lean_lia.TestLIA.test_f) ... skipped 'requires the pinned Lean toolchain'

----------------------------------------------------------------------
Ran 6 tests in 1.0s
"""


def record(benchmark, cell, status, logic="QF_LIA", **fields):
    return dict({"benchmark": benchmark, "cell": cell, "status": status, "logic": logic}, **fields)


class TestLeanProofSummary(unittest.TestCase):
    def setUp(self):
        self.directory = tempfile.TemporaryDirectory()
        self.addCleanup(self.directory.cleanup)
        self.root = Path(self.directory.name).resolve()
        self.corpus = self.root / "corpus"
        (self.corpus / "QF_LIA").mkdir(parents=True)
        self.log = self.root / "unittest.log"
        self.log.write_text(_UNITTEST_LOG)

    def write_jsonl(self, name, records):
        path = self.root / name
        path.write_text("".join(json.dumps(r) + "\n" for r in records))
        return path

    def summarize(self, checks, gate=(), probe=None):
        tsv = self.root / "checks.tsv"
        tsv.write_text("".join("\t".join(str(field) for field in check) + "\n" for check in checks))
        command = [sys.executable, str(_ROOT / "scripts" / "lean_proof_summary.py"), "--checks", str(tsv),
                   "--source", str(_ROOT), "--z3test", str(self.root), "--gate",
                   str(self.write_jsonl("gate.jsonl", gate)), "--context", "z3 abc123"]
        if probe is not None:
            command += ["--probe", str(self.write_jsonl("probe.jsonl", probe)), "--probe-timeout", "10",
                        "--probe-lean-timeout", "120", "--corpus", "z3test sample=%s" % self.corpus]
        return subprocess.run(command, capture_output=True, text=True, check=True).stdout

    def test_unittest_log_is_counted_by_module_with_skip_reasons(self):
        modules, skips = lean_proof_summary.parse_unittest_log(_UNITTEST_LOG)
        self.assertEqual(dict(modules["test_proof_to_lean_uf"]), {"passed": 2})
        self.assertEqual(dict(modules["test_proof_to_lean_lia"]), {"skipped": 2, "failed": 2})
        self.assertEqual(dict(skips), {"requires the pinned Lean toolchain": 2})

    def test_supported_fragments_are_read_from_the_reconstructor(self):
        self.assertIn("propositional", lean_proof_summary.supported_fragments(_ROOT))
        self.assertEqual(lean_proof_summary.supported_fragments(self.root), [])

    def test_reasons_drop_instance_names_and_numbers(self):
        classify = lean_proof_summary.classify
        first = record("a.smt2", "smt-clause-log-nopp", "unsupported",
                       error="unsupported arithmetic declaration: x at node 12")
        second = record("b.smt2", "smt-clause-log-nopp", "unsupported",
                        error="unsupported arithmetic declaration: y_7 at node 3")
        self.assertEqual(classify(first), classify(second))
        self.assertEqual(classify(record("c.smt2", "legacy-proof-object", "unsupported",
                                         error="unsupported sort: Array(Index, Element)"))[1],
                         "unsupported sort: Array(Index, Element)")
        self.assertEqual(classify(record("c.smt2", "smt-clause-log-nopp", "not-applicable", result="unknown")),
                         ("not-applicable", "z3 did not report unsat (result: unknown)", False))

    def test_lean_resource_limits_are_not_reported_as_defects(self):
        classify = lean_proof_summary.classify
        heartbeats = ("Build completed successfully (4 jobs).\nChecking /tmp/a/proof.lean\n/tmp/a/proof.lean:2102:2: "
                      "error: (deterministic) timeout at `isDefEq`, maximum number of heartbeats (1000000) has "
                      "been reached")
        self.assertEqual(classify(record("a.smt2", "smt-clause-log-nopp", "checker-rejected", error=heartbeats)),
                         ("Lean limit", "Lean heartbeat limit (maxHeartbeats) reached", False))
        memory = "/tmp/x/p.lean:50179:4: error: (kernel) excessive memory consumption detected"
        self.assertEqual(classify(record("a.smt2", "legacy-proof-object", "checker-rejected", error=memory))[0],
                         "Lean limit")
        steps = "/tmp/x/p.lean:6467:7: error: `simp` failed: maximum number of steps exceeded"
        self.assertEqual(classify(record("a.smt2", "legacy-proof-object", "checker-rejected", error=steps)),
                         ("Lean limit", "simp step limit (maxSteps) reached", False))
        status, reason, defect = classify(record("a.smt2", "legacy-proof-object", "checker-rejected",
                                                 error="Lean worker exited with code -9"))
        self.assertIn("out-of-memory killer", reason)
        self.assertTrue(defect)
        rejected = ("Build completed successfully (4 jobs).\nChecking /tmp/b/proof.lean\n/tmp/b/proof.lean:12:16: "
                    "error: type mismatch\n  h_17\nhas type False")
        self.assertEqual(classify(record("b.smt2", "legacy-proof-object", "checker-rejected", error=rejected)),
                         ("checker-rejected", "type mismatch", True))
        unknown = ("/tmp/c/p.lean:47489:16: error: (kernel) unknown constant '_private._stdin.0.Z3Proofs."
                   "NativeCertificate.p606121f90916e6540451514ec29647983735408277ddc06577b2e3d9d3737e4d.th_lemma_19094'")
        status, reason, defect = classify(record("c.smt2", "smt-clause-log-nopp", "checker-rejected", error=unknown))
        self.assertEqual(reason, "(kernel) unknown constant 'th_lemma_N' "
                                 "(follows an earlier failed lemma; see the artifact)")
        self.assertTrue(defect)

    def test_gate_failure_is_reported_with_tests_and_benchmarks(self):
        gate = [record("/x/lra_farkas.smt2", "smt-clause-log-nopp", "lean-verified", logic="QF_LRA",
                       fragment="qf_lra", solve_time=0.1, check_time=2.0, proof_size=1234,
                       rules={"th-lemma": 3, "unit-resolution": 5}),
                record("/x/boolean_rewrite.smt2", "legacy-proof-object", "checker-rejected",
                       logic="logic_unknown", error="Lean rejected step 4")]
        text = self.summarize([("Lean reconstruction tests", "unittest", "gate", 1, 75, self.log),
                               ("Boolean matrix", "matrix", "gate", 1, 3, "")], gate=gate)
        self.assertIn("## Lean proof checks: **FAILED**", text)
        self.assertIn("z3 abc123", text)
        self.assertIn("| Lean reconstruction tests | yes | **FAIL** (exit 1) | 1m15s |", text)
        self.assertIn("**Trusted:**", text)
        self.assertIn("`test_proof_to_lean_uf`", text)
        self.assertIn("Tests for the QF_UF slice of the Lean reconstruction", text)
        self.assertIn("requires the pinned Lean toolchain (2)", text)
        self.assertIn("unit-resolution 5, th-lemma 3", text)
        self.assertIn("- `boolean_rewrite.smt2` (legacy proof object): Lean rejected step N", text)
        self.assertNotIn("Boundary probe", text)

    def test_uncertified_probe_inputs_do_not_fail_the_run_but_defects_are_listed(self):
        bench = str(self.corpus / "QF_LIA" / "%s.smt2")
        probe = [record(bench % "a", "reference", "reference", result="unsat"),
                 record(bench % "a", "legacy-proof-object", "lean-verified"),
                 record(bench % "a", "smt-clause-log-nopp", "timeout", error="Lean checking timed out"),
                 record(bench % "b", "reference", "timeout", result=None),
                 record(bench % "b", "legacy-proof-object", "unsupported",
                        error="only quantifier-free expressions are supported"),
                 record(bench % "b", "smt-clause-log-nopp", "checker-rejected", error="step 7 does not follow")]
        text = self.summarize([("Lean reconstruction tests", "unittest", "gate", 0, 5, self.log),
                               ("Boundary probe", "probe", "probe", 1, 600, "")], probe=probe)
        self.assertIn("## Lean proof checks: passed", text)
        self.assertIn("| Boundary probe | no (informational) | done | 10m00s |", text)
        self.assertIn("**1 of 2** benchmarks were lean-verified", text)
        self.assertIn("| z3test sample | QF_LIA | 2 | 1 | 1 | 1 lean-verified, 1 unsupported | "
                      "1 timeout, **1 checker-rejected** |", text)
        self.assertIn("only quantifier-free expressions are supported", text)
        self.assertIn("- `b.smt2` (clause log, checker-rejected): step 7 does not follow", text)

    def test_probe_only_run_is_titled_by_corpus_and_skips_the_scope(self):
        bench = str(self.corpus / "QF_LIA" / "a.smt2")
        probe = [record(bench, "reference", "reference", result="unsat"),
                 record(bench, "legacy-proof-object", "lean-verified")]
        text = self.summarize([("Boundary probe", "probe", "probe", 0, 60, "")], probe=probe)
        self.assertIn("## Lean boundary probe: z3test sample: done", text)
        self.assertNotIn("**Trusted:**", text)
        self.assertIn("**1 of 1** benchmarks were lean-verified", text)

    def test_probe_harness_error_fails_the_run(self):
        text = self.summarize([("Boundary probe", "probe", "probe", 2, 1, "")], probe=[])
        self.assertIn("## Lean boundary probe: z3test sample: **FAILED**", text)
        self.assertIn("| Boundary probe | no (informational) | **FAIL** (exit 2) | 1s |", text)


if __name__ == "__main__":
    unittest.main()
