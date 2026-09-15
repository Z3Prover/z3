"""Tests for study integrity; no additional test framework or solver dependency."""
from pathlib import Path
import json
import subprocess
import sys
import tempfile
from types import SimpleNamespace
import unittest

sys.path.insert(0, str(Path(__file__).resolve().parents[1]))
import resplit_ablation as study


class StudyTests(unittest.TestCase):
    def problem(self, body, extra=""):
        return (f'(declare-const x String)\n{extra}\n(assert {body})\n(check-sat)\n').encode()

    def test_matrix_changes_only_group(self):
        spec, configs = study.configurations()
        self.assertEqual(9, len(configs))
        self.assertEqual("all-on", spec["baseline"])
        expected_labels = {
            "all-on": (True, True, True),
            "no-parikh": (False, True, True),
            "no-equation-regex": (True, False, True),
            "no-reversal": (True, True, False),
            "p0-e0-r1": (False, False, True),
            "p0-e1-r0": (False, True, False),
            "p1-e0-r0": (True, False, False),
            "all-off": (False, False, False),
            "no-factorization": (True, True, True),
        }
        self.assertEqual(set(expected_labels), set(configs))
        baseline = dict(x.split("=", 1) for x in configs["all-on"])
        for entry in spec["configurations"]:
            self.assertEqual(expected_labels[entry["name"]], tuple(entry[g] for g in "PER"))
            values = dict(x.split("=", 1) for x in configs[entry["name"]])
            self.assertEqual(values["smt.string_solver"], "nseq")
            for p in ("monadic_leaf", "monadic_landing", "monadic_split", "view_length_constraints"):
                self.assertEqual("true", values["smt.nseq." + p])
            changed = {key for key in baseline if baseline[key] != values[key]}
            expected = {spec["groups"][g] for g in "PER" if not entry[g]}
            expected.update(entry.get("overrides", {}))
            self.assertEqual(expected, changed)

    def test_lexer_does_not_read_comments_or_strings_as_constraints(self):
        data = self.problem('(str.in_re x (str.to_re "x""(str.len x);(= x y)"))',
                            "; (assert (= (str.len x) 5))\n; (check-sat)")
        info, _ = study.inspect_problem(data)
        self.assertEqual("pure-membership", info["category"])
        info, _ = study.inspect_problem(
            b'(declare-const |str.len| String)(assert (= |str.len| "a"))(check-sat)')
        self.assertEqual("equations", info["category"])

    def test_conservative_metadata(self):
        cases = [
            (self.problem('(= x "a")'), "equations"),
            (self.problem('(= (str.len x) 2)'), "lengths"),
            (self.problem('(and (= x "a") (= (str.len x) 1))'), "equations-and-lengths"),
            (self.problem('(f x)', '(define-fun f ((y String)) Bool (= y "a"))'), "unclassified"),
            (self.problem('(forall ((y String)) (= x y))'), "unclassified"),
            (self.problem('(str.in_re x (re.* (str.to_re "a")))'), "pure-membership"),
        ]
        for data, expected in cases:
            with self.subTest(data=data):
                self.assertEqual(expected, study.inspect_problem(data)[0]["category"])

    def test_reject_queries_and_options(self):
        valid = self.problem('(= x "a")')
        cases = [valid + b"(check-sat)", valid + b"(assert true)",
                 b"(push 1)" + valid, b"(reset)" + valid,
                 b"(set-option :timeout 999)" + valid,
                 b"(set-option :smt.nseq.reverse_retry false)" + valid,
                 valid.replace(b"(check-sat)", b"(check-sat-assuming ())"),
                 b'(assert (= x "unterminated))', b")(",
                 b"(set-info :status sat)(set-info :status unsat)" + valid]
        for data in cases:
            with self.subTest(data=data):
                with self.assertRaises(ValueError):
                    study.inspect_problem(data)

    def test_presentation_removal_is_explicit(self):
        data = b"(set-option :produce-models true)" + self.problem('(= x "a")') + b"(get-model)(exit)"
        info, prepared = study.inspect_problem(data)
        self.assertIn("get-model", info["removed_commands"])
        self.assertNotIn(b"get-model", prepared)
        self.assertIn(b"(get-info :reason-unknown)", prepared)

    def test_duplicate_tokens_not_status_or_comments(self):
        a = self.problem('(= x "a")')
        b = b"; ignored\n(set-info :status sat)" + a.replace(b"(=", b"( = ")
        self.assertEqual(study.inspect_problem(a)[0]["formula_sha256"],
                         study.inspect_problem(b)[0]["formula_sha256"])

    def test_duplicate_annotation_reaches_selected_representative(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp) / "corpus"
            root.mkdir()
            (root / "a.smt2").write_bytes(self.problem('(= x "a")'))
            (root / "b.smt2").write_bytes(b"(set-info :status sat)" + self.problem('(= x "a")'))
            subprocess.run(["git", "init", "-q", str(root)], check=True)
            subprocess.run(["git", "-C", str(root), "config", "core.autocrlf", "false"], check=True)
            subprocess.run(["git", "-C", str(root), "add", "."], check=True)
            subprocess.run(["git", "-C", str(root), "-c", "user.name=Test",
                            "-c", "user.email=test@example.invalid",
                            "commit", "-qm", "fixture"], check=True)
            sha = study.git(root, "rev-parse", "HEAD").decode().strip()
            out = Path(tmp) / "plan"
            study.prepare(SimpleNamespace(corpus=root, corpus_sha=sha, out=out,
                                          config=study.CONFIG, limit=None))
            manifest = json.loads((out / "manifest.json").read_text())
            self.assertEqual(1, len(manifest["selected"]))
            self.assertEqual("a.smt2", manifest["selected"][0]["path"])
            self.assertEqual("sat", manifest["selected"][0]["expected"])

    def test_result_errors_never_hidden_by_sat(self):
        cases = [(b"sat\n(error \"bad option\")", b"", 0, False, "error"),
                 (b"sat", b"ERROR: invalid model", 0, False, "error"),
                 (b"sat", b"", 1, False, "error"),
                 (b"sat\nunsat", b"", 0, False, "error"),
                 (b"sat\nsat", b"", 0, False, "error"),
                 (b"", b"", 0, False, "error"),
                 (b"unknown\n(:reason-unknown \"incomplete\")", b"", 0, False, "unknown"),
                 (b"unknown\n(:reason-unknown \"timeout\")", b"", 0, False, "timeout"),
                 (b"sat", b"", -9, True, "timeout"),
                 (b"sat\n(:reason-unknown \"\")", b"", 0, False, "sat")]
        for out, err, code, killed, expected in cases:
            self.assertEqual(expected, study.parse_result(out, err, code, killed)[0])

    def test_raw_timeout_output_retained(self):
        with tempfile.TemporaryDirectory() as tmp:
            prefix = Path(tmp) / "slow"
            row = study.execute([sys.executable, "-c",
                                 "import time; print('partial', flush=True); time.sleep(20)"], 0.3, prefix)
            self.assertEqual("timeout", row["status"])
            self.assertIn(b"partial", prefix.with_suffix(".stdout").read_bytes())
            self.assertTrue(prefix.with_suffix(".stderr").exists())

    def test_pairs_and_contradictions(self):
        def row(config, status, seconds, repeat=0):
            return dict(id="0", repeat=repeat, config=config, status=status, seconds=seconds,
                        expected="", verdicts=[status], family="f", category="equations", reason="")
        rows = [row("all", "sat", 1), row("off", "timeout", 10),
                row("all", "sat", 2, 1), row("off", "sat", 4, 1)]
        s = study.summarize(rows, {}, ["all", "off"], "all", 10)
        self.assertEqual(2, s["paired"]["off"]["geomean_other_over_baseline_joint_only"])
        self.assertEqual(24, s["paired"]["off"]["par2_other_seconds"])
        self.assertEqual(1, s["paired"]["off"]["baseline_only_decided"])
        self.assertTrue(s["valid_for_comparison"])
        partial = study.summarize(rows[:1], {}, ["all", "off"], "all", 10, expected_runs=4)
        self.assertFalse(partial["complete"])
        self.assertFalse(partial["valid_for_comparison"])
        rows[-1] = row("off", "unsat", 4, 1)
        self.assertFalse(study.summarize(rows, {}, ["all", "off"], "all", 10)["valid_for_comparison"])

    def make_blocks(self, tmp):
        spec, configs = study.configurations()
        entry = dict(id="000000", path="f/a.smt2", family="f", category="equations", expected="")
        manifest = dict(corpus="local", repository="local", fatal=[], selected=[entry])
        env = dict(platform="test", machine="x64", hostname="runner", processor="cpu",
                   cpu_count=8, timeout_seconds=10, memory_mb=512, memory_policy="allocator",
                   jobs=1, repeats=1)
        record = dict(source_identity={"head": "a" * 40}, binary_sha256="b" * 64, build_evidence={})
        names = list(configs)
        roots = [Path(tmp) / "first", Path(tmp) / "second"]
        for root, arms in zip(roots, (names[:4], names[4:])):
            (root / "build-record").mkdir(parents=True)
            for name, value in (("manifest.json", manifest), ("configurations.json", spec),
                                ("environment.json", env), ("build-record/build.json", record)):
                study.write_json(root / name, value)
            rows = [{**entry, "config": arm, "repeat": 0, "status": "sat", "seconds": 1.0,
                     "returncode": 0, "reason": "", "verdicts": ["sat"]} for arm in arms]
            (root / "runs.jsonl").write_text("".join(json.dumps(r) + "\n" for r in rows))
            study.write_json(root / "summary.json",
                             study.summarize(rows, manifest, arms, spec["baseline"], 10, len(rows)))
        return roots

    def test_merge_complete_configuration_blocks(self):
        with tempfile.TemporaryDirectory() as tmp:
            roots = self.make_blocks(tmp)
            out = Path(tmp) / "combined"
            study.merge_results(SimpleNamespace(results=roots, out=out))
            summary = json.loads((out / "summary.json").read_text())
            self.assertTrue(summary["valid_for_comparison"])
            self.assertEqual(9, summary["completed_runs"])
            self.assertEqual(8, len(summary["paired"]))
            self.assertEqual(1, summary["paired"]["no-parikh"]["jointly_decided_same_verdict"])
            self.assertEqual(2, len(json.loads((out / "sources.json").read_text())["sources"]))

    def test_merge_rejects_incompatible_build_or_limits(self):
        for filename, key, value in (("build-record/build.json", "binary_sha256", "c" * 64),
                                     ("environment.json", "memory_mb", 1024),
                                     ("environment.json", "hostname", "different-runner"),
                                     ("summary.json", "complete", False)):
            with self.subTest(filename=filename, key=key), tempfile.TemporaryDirectory() as tmp:
                roots = self.make_blocks(tmp)
                path = roots[1] / filename
                data = json.loads(path.read_text())
                data[key] = value
                study.write_json(path, data)
                with self.assertRaises(ValueError):
                    study.merge_results(SimpleNamespace(results=roots, out=Path(tmp) / "combined"))

    def test_merge_rejects_missing_and_duplicate_arms(self):
        with tempfile.TemporaryDirectory() as tmp:
            roots = self.make_blocks(tmp)
            with self.assertRaises(ValueError):
                study.merge_results(SimpleNamespace(results=roots[:1], out=Path(tmp) / "missing"))
            with self.assertRaises(ValueError):
                study.merge_results(SimpleNamespace(results=roots + roots[:1], out=Path(tmp) / "duplicate"))

    def test_merge_retains_invalid_provenance_verdict(self):
        with tempfile.TemporaryDirectory() as tmp:
            roots = self.make_blocks(tmp)
            path = roots[0] / "summary.json"
            summary = json.loads(path.read_text())
            summary["valid_for_comparison"] = False
            summary["issues"].append({"error": "source changed during measurements"})
            study.write_json(path, summary)
            out = Path(tmp) / "invalid"
            with self.assertRaises(ValueError):
                study.merge_results(SimpleNamespace(results=roots, out=out))
            self.assertFalse(json.loads((out / "summary.json").read_text())["valid_for_comparison"])


if __name__ == "__main__":
    unittest.main()
