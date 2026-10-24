"""Tests for corpus selection, verdict accounting, resource bounds, and reports."""

import argparse
import contextlib
import hashlib
import io
import json
from pathlib import Path
import sys
import tempfile
import unittest
from unittest.mock import patch

import run_checker_regressions as runner


class CheckerRegressionTests(unittest.TestCase):
    def manifested_corpus(self, directory):
        corpus = Path(directory) / "corpus"
        corpus.mkdir()
        cases = []
        for logic in ("QF_UF", "QF_LIA"):
            path = corpus / logic / "example.smt2"
            path.parent.mkdir()
            path.write_bytes(b"(assert false)\n(check-sat)\n")
            cases.append({"path": path.relative_to(corpus).as_posix(), "logic": logic,
                          "sha256": hashlib.sha256(path.read_bytes()).hexdigest()})
        manifest = corpus / "manifest.json"
        document = {"schema_version": 1, "source": "official-test-source", "seed": 42,
                    "per_logic": 1, "archives": [{"logic": row["logic"]} for row in cases],
                    "cases": cases}
        manifest.write_text(json.dumps(document))
        args = argparse.Namespace(
            corpus=corpus, corpus_path=".", max_cases=0, checker=Path("checker"),
            output=Path(directory) / "report", corpus_commit="test", memory_limit_mb=0,
            total_timeout_seconds=10, case_timeout_seconds=1, solver_timeout_ms=1,
            manifest=manifest, expected_cases=2)
        return args, document

    def test_verdict_requires_matching_exit_code_and_stdout(self):
        for code, text, expected in (
                (0, "ACCEPT\n", "ACCEPT"), (1, "REJECT", "REJECT"),
                (3, "PARTIAL 4", "PARTIAL"), (4, "SAT", "SAT"),
                (5, "UNKNOWN timeout", "UNKNOWN"), (2, "", "ERROR"),
                (-11, "", "CRASH"), (134, "", "CRASH"),
                (0, "SAT", "PROTOCOL_ERROR"), (0, "", "PROTOCOL_ERROR"),
                (1, "ACCEPT", "PROTOCOL_ERROR"), (3, "PARTIAL 0", "PROTOCOL_ERROR"),
                (5, "UNKNOWN", "PROTOCOL_ERROR"),
                (0, "ACCEPT\nSAT", "PROTOCOL_ERROR")):
            with self.subTest(code=code, text=text):
                self.assertEqual(runner.classify(code, text), expected)

    def test_selection_is_recursive_sorted_bounded_and_not_manifest_driven(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            (root / "nested").mkdir()
            for name in ("b.smt2", "a.smt2", "nested/c.smt2", "list.txt", "saved.proof"):
                (root / name).touch()
            paths, total = runner.discover(root, ".", 2)
            self.assertEqual(total, 3)
            self.assertEqual([path.name for path in paths], ["a.smt2", "b.smt2"])
            self.assertEqual(len(runner.discover(root, ".", 0)[0]), 3)
            with self.assertRaises(ValueError):
                runner.discover(root, "..", 0)
            with self.assertRaises(ValueError):
                runner.discover(root, "missing", 0)
            (root / "empty").mkdir()
            with self.assertRaises(ValueError):
                runner.discover(root, "empty", 0)

    def test_process_execution_preserves_logs_and_statistics(self):
        with tempfile.TemporaryDirectory() as directory:
            output = Path(directory)
            (output / "logs").mkdir()
            row = runner.run_case(
                [sys.executable, "-c",
                 "import sys; print('ACCEPT'); "
                 "print('solve_ms=1.250 marshal_ms=2.500 check_ms=0.500 "
                 "expressions=7 declarations=3 proof_nodes=9', file=sys.stderr)"],
                "test.smt2", output, 0, 10, 0)
            self.assertEqual(row["outcome"], "ACCEPT")
            self.assertGreater(row["wall_seconds"], 0)
            self.assertEqual(row["statistics"]["marshal_ms"], 2.5)
            self.assertEqual(row["statistics"]["proof_nodes"], 9)
            self.assertEqual((output / row["stdout"]).read_text().strip(), "ACCEPT")

    def test_process_statistics_accept_native_semantics_suffix(self):
        with tempfile.TemporaryDirectory() as directory:
            output = Path(directory)
            (output / "logs").mkdir()
            for index, semantics in enumerate(("legacy", "sorted-datatype", "sorted-core")):
                row = runner.run_case(
                    [sys.executable, "-c",
                     "import sys; print('PARTIAL 2'); "
                     "print('solve_ms=1.250 marshal_ms=2.500 check_ms=0.500 "
                     f"expressions=7 declarations=3 proof_nodes=9 semantics={semantics}', "
                     "file=sys.stderr); sys.exit(3)"],
                    "test.smt2", output, index, 10, 0)
                self.assertEqual(row["outcome"], "PARTIAL")
                self.assertEqual(row["statistics"]["semantics"], semantics)
                self.assertEqual(row["statistics"]["proof_nodes"], 9)
                self.assertEqual(row["statistics"]["solve_ms"], 1.25)

    def test_diagnostics_validate_counts_and_read_beyond_log_preview(self):
        with tempfile.TemporaryDirectory() as directory:
            path = Path(directory) / "stderr"
            path.write_text("x" * 65536 + "\n"
                            "diagnostic\tchecked\tpending=3\tfamilies=1\n"
                            "obligation\tth-lemma\t3\t17\tHolds:Int\n")
            diagnostic = runner.read_diagnostics(path)
            self.assertEqual(diagnostic["pending"], 3)
            self.assertEqual(diagnostic["obligations"][0]["first_index"], 17)
            path.write_text("diagnostic\tchecked\tpending=4\tfamilies=1\n"
                            "obligation\tth-lemma\t3\t17\tHolds:Int\n")
            with self.assertRaisesRegex(ValueError, "Inconsistent"):
                runner.read_diagnostics(path)
            path.write_text("diagnostic\trejected\tstage=Root\tindex=17\n")
            self.assertEqual(runner.read_diagnostics(path)["rejection"],
                             ["stage=Root", "index=17"])
            path.write_text("")
            with self.assertRaisesRegex(ValueError, "Missing"):
                runner.read_diagnostics(path)

    def test_separate_diagnostics_preserve_coverage_and_rank_matching_proofs(self):
        with tempfile.TemporaryDirectory() as directory:
            args, _ = self.manifested_corpus(directory)
            args.output.mkdir()
            paths, _ = runner.discover(args.corpus, ".", 0)
            selection = {"solver_timeout_ms": 10, "case_timeout_seconds": 2,
                         "memory_limit_mb": 0,
                         **runner.verify_manifest(args.corpus, ".", args.manifest, paths)}
            (args.output / "selection.json").write_text(json.dumps(selection))
            results = [{"path": "QF_LIA/example.smt2", "outcome": "PARTIAL", "verdict": "PARTIAL 3"},
                       {"path": "QF_UF/example.smt2", "outcome": "ACCEPT", "verdict": "ACCEPT"}]
            results_path = args.output / "results.jsonl"
            results_path.write_text("".join(json.dumps(row) + "\n" for row in results))
            original = results_path.read_bytes()

            def replay(command, path, output, index, timeout, megabytes, log_directory):
                self.assertIn("--diagnostics", command)
                self.assertEqual(timeout, 4)
                stderr = f"{log_directory}/{index:06d}.stderr"
                (output / stderr).write_text("diagnostic\tchecked\tpending=3\tfamilies=1\n"
                                            "obligation\tth-lemma\t3\t17\tHolds:Int\n")
                return {"path": path, "outcome": "PARTIAL", "verdict": "PARTIAL 3", "stderr": stderr}

            with patch.object(runner, "run_case", side_effect=replay) as run, \
                    contextlib.redirect_stdout(io.StringIO()):
                self.assertEqual(runner.diagnose(args), 0)
                self.assertEqual(run.call_count, 1)
            self.assertEqual(results_path.read_bytes(), original)
            runner.report(args.output)
            summary = json.loads((args.output / "summary.json").read_text())
            self.assertEqual(summary["counts"]["PARTIAL"], 1)
            self.assertEqual(summary["counts"]["ACCEPT"], 1)
            self.assertEqual(summary["obligation_families"][0]["sole_family_proofs"], 1)
            self.assertEqual(summary["obligation_families"][0]["obligations"], 3)
            self.assertIn("Remaining obligation families", (args.output / "report.md").read_text())
            rows = [json.loads((args.output / "diagnostics.jsonl").read_text())]
            rows[0]["matches_original"] = False
            self.assertEqual(runner.obligation_coverage(rows), [])

    def test_diagnostic_errors_do_not_change_original_coverage(self):
        with tempfile.TemporaryDirectory() as directory:
            args, _ = self.manifested_corpus(directory)
            args.output.mkdir()
            (args.output / "selection.json").write_text(json.dumps({
                "solver_timeout_ms": 10, "case_timeout_seconds": 2, "memory_limit_mb": 0}))
            result = {"path": "QF_LIA/example.smt2", "outcome": "PARTIAL", "verdict": "PARTIAL 3"}
            (args.output / "results.jsonl").write_text(json.dumps(result) + "\n")

            def replay(*unused, **kwargs):
                stderr = "diagnostic-logs/000000.stderr"
                (args.output / stderr).write_text("diagnostic\tchecked\tpending=2\tfamilies=1\n"
                                                "obligation\tth-lemma\t2\t1\tshape\n")
                return {**result, "stderr": stderr}

            with patch.object(runner, "run_case", side_effect=replay), \
                    contextlib.redirect_stdout(io.StringIO()):
                self.assertEqual(runner.diagnose(args), 1)
            runner.report(args.output)
            summary = json.loads((args.output / "summary.json").read_text())
            self.assertEqual(summary["diagnostic_errors"], 1)
            self.assertEqual(summary["obligation_families"], [])
            self.assertEqual(summary["counts"]["PARTIAL"], 1)
            self.assertEqual(summary["counts"]["ERROR"], 0)
            with (args.output / "diagnostics.jsonl").open("a") as stream:
                stream.write('{"path":')
            runner.report(args.output)
            summary = json.loads((args.output / "summary.json").read_text())
            self.assertEqual(summary["diagnostic_errors"], 1)
            self.assertEqual(len(summary["warnings"]), 1)

    def test_manifest_verifies_all_input_hashes_and_membership(self):
        with tempfile.TemporaryDirectory() as directory:
            args, _ = self.manifested_corpus(directory)
            paths, _ = runner.discover(args.corpus, ".", 0)
            metadata = runner.verify_manifest(args.corpus, ".", args.manifest, paths)
            self.assertEqual(len(metadata["input_sha256"]), 2)
            self.assertEqual(metadata["manifest"]["per_logic"], 1)
            self.assertEqual(metadata["manifest"]["sha256"],
                             hashlib.sha256(args.manifest.read_bytes()).hexdigest())
            paths[0].write_bytes(b"(assert true)\n")
            with self.assertRaisesRegex(ValueError, "SHA-256 mismatch"):
                runner.verify_manifest(args.corpus, ".", args.manifest, paths)

    def test_manifest_rejects_missing_extra_duplicate_and_unsafe_inputs(self):
        with tempfile.TemporaryDirectory() as directory:
            args, original = self.manifested_corpus(directory)
            paths, _ = runner.discover(args.corpus, ".", 0)
            for change in ("missing", "duplicate", "escape", "absolute", "backslash",
                           "bad-hash", "bad-version", "wrong-per-logic"):
                document = json.loads(json.dumps(original))
                if change == "missing":
                    document["cases"].pop()
                elif change == "duplicate":
                    document["cases"].append(document["cases"][0])
                elif change == "escape":
                    document["cases"][0]["path"] = "../outside.smt2"
                elif change == "absolute":
                    document["cases"][0]["path"] = paths[0].as_posix()
                elif change == "backslash":
                    document["cases"][0]["path"] = "QF_UF\\example.smt2"
                elif change == "bad-hash":
                    document["cases"][0]["sha256"] = "not-a-hash"
                elif change == "bad-version":
                    document["schema_version"] = 2
                else:
                    document["per_logic"] = 25
                args.manifest.write_text(json.dumps(document))
                with self.subTest(change=change), self.assertRaises(ValueError):
                    runner.verify_manifest(args.corpus, ".", args.manifest, paths)
            args.manifest.write_text(json.dumps(original))
            extra = args.corpus / "extra.smt2"
            extra.touch()
            paths, _ = runner.discover(args.corpus, ".", 0)
            with self.assertRaisesRegex(ValueError, "exactly the discovered"):
                runner.verify_manifest(args.corpus, ".", args.manifest, paths)
            with self.assertRaisesRegex(ValueError, "inside the selected"):
                runner.verify_manifest(args.corpus, ".", Path(directory) / "manifest.json", paths)

    def test_manifest_supports_unequal_logic_cohorts_and_reports_sizes(self):
        with tempfile.TemporaryDirectory() as directory:
            args, document = self.manifested_corpus(directory)
            extra = args.corpus / "QF_UF" / "second.smt2"
            extra.write_bytes(b"(assert false)\n(check-sat)\n")
            document["cases"].append({
                "path": "QF_UF/second.smt2", "logic": "QF_UF",
                "sha256": hashlib.sha256(extra.read_bytes()).hexdigest()})
            document["per_logic"] = {"QF_UF": 2, "QF_LIA": 1}
            args.manifest.write_text(json.dumps(document))
            paths, _ = runner.discover(args.corpus, ".", 0)
            metadata = runner.verify_manifest(args.corpus, ".", args.manifest, paths)
            args.output.mkdir()
            (args.output / "selection.json").write_text(json.dumps({
                "paths": [path.relative_to(args.corpus).as_posix() for path in paths],
                **metadata}))
            runner.report(args.output)
            self.assertIn("QF_LIA: 1, QF_UF: 2 inputs",
                          (args.output / "report.md").read_text())
            for sizes in ({"QF_UF": 1, "QF_LIA": 1}, {"QF_UF": 2},
                          {"QF_UF": 2, "QF_LIA": 1, "UF": 1}):
                document["per_logic"] = sizes
                args.manifest.write_text(json.dumps(document))
                with self.subTest(sizes=sizes), self.assertRaisesRegex(ValueError, "sample size"):
                    runner.verify_manifest(args.corpus, ".", args.manifest, paths)

    def test_manifest_provenance_and_per_logic_results_are_reported(self):
        with tempfile.TemporaryDirectory() as directory:
            args, _ = self.manifested_corpus(directory)
            rows = [{"path": "QF_LIA/example.smt2", "outcome": "ACCEPT"},
                    {"path": "QF_UF/example.smt2", "outcome": "UNKNOWN"}]
            with patch.object(runner.subprocess, "run",
                              return_value=argparse.Namespace(stdout="test-version")), \
                    patch.object(runner, "run_case", side_effect=rows), \
                    contextlib.redirect_stdout(io.StringIO()):
                self.assertEqual(runner.run_suite(args), 0)
            runner.report(args.output)
            self.assertEqual((args.output / "input-manifest.json").read_bytes(),
                             args.manifest.read_bytes())
            summary = json.loads((args.output / "summary.json").read_text())
            self.assertEqual(summary["selection"]["manifest"]["seed"], 42)
            self.assertEqual(summary["per_logic"]["QF_LIA"]["counts"]["ACCEPT"], 1)
            self.assertEqual(summary["per_logic"]["QF_UF"]["counts"]["UNKNOWN"], 1)
            self.assertEqual(summary["success_rate"], 0.5)
            self.assertIn("Per-logic coverage", (args.output / "report.md").read_text())
            self.assertIn("input_sha256", (args.output / "results.csv").read_text())

    def test_manifest_budget_exhaustion_after_one_case_fails_the_run(self):
        with tempfile.TemporaryDirectory() as directory:
            args, _ = self.manifested_corpus(directory)
            args.total_timeout_seconds = 1
            with patch.object(runner.subprocess, "run",
                              return_value=argparse.Namespace(stdout="test-version")), \
                    patch.object(runner, "run_case",
                                 return_value={"path": "QF_LIA/example.smt2", "outcome": "ACCEPT"}), \
                    patch.object(runner.time, "perf_counter", side_effect=[0, 0, 2]), \
                    contextlib.redirect_stdout(io.StringIO()):
                self.assertEqual(runner.run_suite(args), 1)
            runner.report(args.output)
            summary = json.loads((args.output / "summary.json").read_text())
            self.assertEqual(summary["per_logic"]["QF_UF"]["counts"]["NOT_RUN"], 1)

    def test_workflow_run_reports_the_checker_revision_not_the_default_branch(self):
        with tempfile.TemporaryDirectory() as directory:
            args, _ = self.manifested_corpus(directory)
            source, default_branch = "a" * 40, "b" * 40
            with patch.dict("os.environ", {"SOURCE_SHA": source, "GITHUB_SHA": default_branch}), \
                    patch.object(runner.subprocess, "run",
                                 return_value=argparse.Namespace(stdout="test-version")), \
                    patch.object(runner, "run_case", side_effect=[
                        {"path": "QF_LIA/example.smt2", "outcome": "ACCEPT"},
                        {"path": "QF_UF/example.smt2", "outcome": "ACCEPT"}]), \
                    contextlib.redirect_stdout(io.StringIO()):
                runner.report(args.output)
                self.assertIn(f"Z3 commit: `{source}`", (args.output / "report.md").read_text())
                self.assertEqual(runner.run_suite(args), 0)
                runner.report(args.output)
            selection = json.loads((args.output / "selection.json").read_text())
            self.assertEqual(selection["z3_commit"], source)
            self.assertIn(f"Z3 commit: `{source}`", (args.output / "report.md").read_text())

    def test_expected_case_count_is_checked_before_executing_the_checker(self):
        with tempfile.TemporaryDirectory() as directory:
            args, _ = self.manifested_corpus(directory)
            args.expected_cases = 225
            with patch.object(runner.subprocess, "run") as run:
                with self.assertRaisesRegex(ValueError, "Expected 225 inputs, selected 2"):
                    runner.run_suite(args)
                run.assert_not_called()

    def test_interrupted_manifest_run_retains_per_logic_unattempted_counts(self):
        with tempfile.TemporaryDirectory() as directory:
            args, _ = self.manifested_corpus(directory)
            paths, _ = runner.discover(args.corpus, ".", 0)
            metadata = runner.verify_manifest(args.corpus, ".", args.manifest, paths)
            args.output.mkdir()
            selection = {"paths": [path.relative_to(args.corpus).as_posix() for path in paths],
                         **metadata}
            (args.output / "selection.json").write_text(json.dumps(selection))
            runner.report(args.output)
            summary = json.loads((args.output / "summary.json").read_text())
            self.assertEqual(summary["tested"], 0)
            self.assertIsNone(summary["success_rate"])
            for group in summary["per_logic"].values():
                self.assertEqual(group["selected"], 1)
                self.assertEqual(group["counts"]["NOT_RUN"], 1)

    def test_whole_process_timeout_kills_the_checker(self):
        with tempfile.TemporaryDirectory() as directory:
            output = Path(directory)
            (output / "logs").mkdir()
            row = runner.run_case(
                [sys.executable, "-c", "import time; time.sleep(30)"],
                "slow.smt2", output, 0, 0.1, 0)
            self.assertEqual(row["outcome"], "TIMEOUT")
            self.assertIsNone(row["returncode"])
            self.assertLess(row["wall_seconds"], 10)

    @unittest.skipUnless(sys.platform == "linux", "Linux address-space limit")
    def test_linux_memory_limit_is_applied_to_the_checker_process(self):
        with tempfile.TemporaryDirectory() as directory:
            output = Path(directory)
            (output / "logs").mkdir()
            row = runner.run_case(
                [sys.executable, "-c",
                 "import resource; assert resource.getrlimit(resource.RLIMIT_AS) == (512*1024**2,)*2; "
                 "print('ACCEPT')"],
                "bounded.smt2", output, 0, 10, 512)
            self.assertEqual(row["outcome"], "ACCEPT")

    def test_report_never_counts_partial_sat_or_unknown_as_success(self):
        with tempfile.TemporaryDirectory() as directory:
            output = Path(directory)
            outcomes = ("ACCEPT", "PARTIAL", "REJECT", "SAT", "UNKNOWN", "TIMEOUT", "ERROR")
            rows = [{"path": f"{index}.smt2", "outcome": outcome, "wall_seconds": index + 1}
                    for index, outcome in enumerate(outcomes)]
            selection = {"paths": [row["path"] for row in rows] + ["interrupted.smt2"]}
            (output / "selection.json").write_text(json.dumps(selection))
            (output / "results.jsonl").write_text(
                "\n".join(json.dumps(row) for row in rows) + "\n")
            runner.report(output)
            summary = json.loads((output / "summary.json").read_text())
            self.assertEqual(summary["tested"], 7)
            self.assertEqual(summary["selected"], 8)
            self.assertEqual(summary["success_rate"], 1 / 7)
            self.assertEqual(summary["uncertified_rate"], 6 / 7)
            self.assertEqual(summary["counts"]["NOT_RUN"], 1)
            self.assertEqual(summary["median_seconds"], 4)
            self.assertEqual(summary["p95_seconds"], 7)
            self.assertIn("Pulse is not linked", (output / "report.md").read_text())
            self.assertIn("interrupted.smt2", (output / "results.csv").read_text())

    def test_report_survives_a_build_failure_with_no_results(self):
        with tempfile.TemporaryDirectory() as directory:
            output = Path(directory)
            (output / "build.json").write_text('{"exit_code":1,"wall_seconds":5}')
            with patch.dict("os.environ", {"BUILD_OUTCOME": "failure"}):
                runner.report(output)
            summary = json.loads((output / "summary.json").read_text())
            self.assertEqual(summary["build"]["exit_code"], 1)
            self.assertIsNone(summary["success_rate"])
            self.assertEqual(summary["tested"], 0)
            text = (output / "report.md").read_text()
            self.assertIn("**failure**", text)
            self.assertIn("no test success is claimed", text)

    def test_budget_exhaustion_records_all_unattempted_inputs(self):
        with tempfile.TemporaryDirectory() as directory:
            corpus = Path(directory) / "corpus"
            corpus.mkdir()
            for name in ("a.smt2", "b.smt2"):
                (corpus / name).touch()
            output = Path(directory) / "report"
            args = argparse.Namespace(
                corpus=corpus, corpus_path=".", max_cases=0, checker=Path("checker"),
                output=output, corpus_commit="test", memory_limit_mb=0,
                total_timeout_seconds=1, case_timeout_seconds=1, solver_timeout_ms=1)
            version = argparse.Namespace(stdout="test-version")
            with patch.object(runner.subprocess, "run", return_value=version), \
                    patch.object(runner.time, "perf_counter", side_effect=[0, 2, 3]), \
                    contextlib.redirect_stdout(io.StringIO()):
                self.assertEqual(runner.run_suite(args), 1)
            runner.report(output)
            summary = json.loads((output / "summary.json").read_text())
            self.assertEqual(summary["counts"]["NOT_RUN"], 2)
            self.assertEqual(summary["tested"], 0)

    def test_interrupted_final_record_is_reported_not_silently_lost(self):
        with tempfile.TemporaryDirectory() as directory:
            output = Path(directory)
            (output / "selection.json").write_text('{"paths":["a.smt2","b.smt2"]}')
            (output / "results.jsonl").write_text(
                '{"path":"a.smt2","outcome":"ACCEPT","wall_seconds":1}\n{"path":')
            runner.report(output)
            summary = json.loads((output / "summary.json").read_text())
            self.assertEqual(summary["counts"]["ACCEPT"], 1)
            self.assertEqual(summary["counts"]["NOT_RUN"], 1)
            self.assertEqual(len(summary["warnings"]), 1)
            self.assertIn("**Warning:**", (output / "report.md").read_text())
            (output / "results.jsonl").write_text("bad record\n")
            with self.assertRaises(json.JSONDecodeError):
                runner.report(output)

    def test_process_errors_fail_the_run_but_coverage_gaps_do_not(self):
        with tempfile.TemporaryDirectory() as directory:
            corpus = Path(directory) / "corpus"
            corpus.mkdir()
            (corpus / "input.smt2").touch()
            args = argparse.Namespace(
                corpus=corpus, corpus_path=".", max_cases=0, checker=Path("checker"),
                output=Path(directory) / "report", corpus_commit="test", memory_limit_mb=0,
                total_timeout_seconds=10, case_timeout_seconds=1, solver_timeout_ms=1)
            for outcome in runner.OUTCOMES[:-1]:
                with self.subTest(outcome=outcome), \
                        patch.object(runner.subprocess, "run",
                                     return_value=argparse.Namespace(stdout="test-version")), \
                        patch.object(runner, "run_case",
                                     return_value={"path": "input.smt2", "outcome": outcome}), \
                        contextlib.redirect_stdout(io.StringIO()):
                    self.assertEqual(runner.run_suite(args), int(outcome in runner.ERRORS))

    def test_resource_arguments_reject_invalid_or_unbounded_values(self):
        for value in ("0", "-1", "inf", "nan"):
            with self.subTest(value=value), self.assertRaises(argparse.ArgumentTypeError):
                runner.positive_float(value)
        for value in ("0", "-1", "4294967296"):
            with self.subTest(value=value), self.assertRaises(argparse.ArgumentTypeError):
                runner.solver_timeout(value)
        with self.assertRaises(argparse.ArgumentTypeError):
            runner.nonnegative_int("-1")


if __name__ == "__main__":
    unittest.main()
