"""Tests for study integrity; no additional test framework or solver dependency."""
from pathlib import Path
import json
import re
import subprocess
import sys
import tempfile
from types import SimpleNamespace
import unittest
from unittest import mock

sys.path.insert(0, str(Path(__file__).resolve().parents[1]))
import resplit_ablation as study


class StudyTests(unittest.TestCase):
    def problem(self, body, extra=""):
        return (f'(declare-const x String)\n{extra}\n(assert {body})\n(check-sat)\n').encode()

    def test_build_record_rejects_stale_or_unidentified_binaries(self):
        pinned = "a" * 40
        versions = ["Z3 build hashcode " + pinned,
                    "Z3 build hashcode " + "b" * 40, "Z3 version 5.1.0"]
        with tempfile.TemporaryDirectory() as folder:
            root = Path(folder)
            source, build = root / "source", root / "build"
            source.mkdir()
            build.mkdir()
            binary = build / "z3"
            binary.write_bytes(b"fixture binary")
            for name in ("CMakeCache.txt", "build.ninja"):
                (build / name).write_text("fixture")
            compiler = build / "CMakeFiles" / "3.30.9" / "CMakeCXXCompiler.cmake"
            compiler.parent.mkdir(parents=True)
            compiler.write_text("fixture compiler")
            identity = {"head": pinned, "untracked_sha256": {}}
            for i, version in enumerate(versions):
                args = SimpleNamespace(source=source, build_dir=build, z3=binary,
                                       out=root / f"record-{i}", native_base_sha=None,
                                       allow_dirty=False, build_command="fixture build")
                responses = [subprocess.CompletedProcess([], 0, version.encode(), b""),
                             subprocess.CompletedProcess([], 0, b"parameters", b"")]
                with self.subTest(version=version), \
                        mock.patch.object(study, "source_identity", return_value=(identity, b"")), \
                        mock.patch.object(study.subprocess, "run", side_effect=responses), \
                        mock.patch("builtins.print"):
                    if i == 0:
                        study.record_build(args)
                        record = json.loads((args.out / "build.json").read_text())
                        self.assertEqual(version, record["version"])
                    else:
                        with self.assertRaisesRegex(ValueError, "does not identify recorded source"):
                            study.record_build(args)

    def test_matrix_changes_only_group(self):
        spec, configs = study.configurations()
        self.assertEqual(3, spec["schema"])
        self.assertEqual("PERF", spec["order"])
        self.assertEqual(5, len(configs))
        self.assertEqual("TTTT", spec["baseline"])
        self.assertEqual(list(study.PERF_FLIPS), list(configs))
        baseline = dict(x.split("=", 1) for x in configs["TTTT"])
        for entry in spec["configurations"]:
            values = dict(x.split("=", 1) for x in configs[entry["name"]])
            self.assertEqual(values["smt.string_solver"], "nseq")
            self.assertNotIn("smt.nseq.parikh_abstraction", values)
            self.assertEqual("true", values["smt.nseq.view_length_constraints"])
            self.assertEqual("true", values["smt.nseq.monadic_leaf"])
            self.assertEqual("false", values["smt.nseq.abelian"])
            for p in ("parikh", "monadic_landing", "monadic_split", "monadic_leaf_refute"):
                self.assertEqual("false", values["smt.nseq." + p])
            self.assertEqual("", values["tactic.default_tactic"])
            self.assertEqual(set(baseline), set(values))
            changed = {key for key in baseline if baseline[key] != values[key]}
            self.assertEqual(set(study.PERF_FLIPS[entry["name"]]), changed)
            self.assertEqual(0 if entry["name"] == spec["baseline"] else 1, len(changed))
            for i, key in enumerate(("regex_parikh", "equation_abstraction", "reverse_retry",
                                     "regex_factorization_threshold")):
                on = entry["name"][i] == "T"
                self.assertEqual(str(int(on)) if i == 3 else str(on).lower(),
                                 values["smt.nseq." + key])

    def test_source_guard_rejects_old_E_default_and_changed_UINT_type(self):
        spec, _ = study.configurations()
        declarations = "\n".join(
            f"('{key[4:]}', {'BOOL' if isinstance(value, bool) else 'UINT'}, {value}, 'fixture'),"
            for key, value in spec["common"].items() if key.startswith("smt.nseq."))
        with tempfile.TemporaryDirectory() as folder:
            root = Path(folder)
            path = root / "src" / "params" / "smt_params_helper.pyg"
            path.parent.mkdir(parents=True)
            path.write_text(declarations)
            study.validate_source_defaults(root, spec)
            for bad in (
                    declarations.replace("'nseq.equation_abstraction', BOOL, True",
                                         "'nseq.equation_abstraction', BOOL, False"),
                    declarations.replace("'nseq.regex_factorization_threshold', UINT, 1",
                                         "'nseq.regex_factorization_threshold', BOOL, True"),
                    declarations.replace("'nseq.reverse_retry'", "'missing_reverse_retry'")):
                path.write_text(bad)
                with self.assertRaisesRegex(ValueError, "source default/type mismatch"):
                    study.validate_source_defaults(root, spec)

    def test_invalid_default_matrix_rejected(self):
        for mutate in (
                lambda s: s["common"].update({"smt.nseq.parikh": True}),
                lambda s: s["common"].update({"smt.nseq.parikh_abstraction": True}),
                lambda s: s["common"].update({"smt.nseq.equation_abstraction": False}),
                lambda s: s["common"].update({"smt.nseq.monadic_leaf": False}),
                lambda s: s["common"].update({"smt.nseq.abelian": True}),
                lambda s: s.update(order="PEFR"),
                lambda s: s["common"].update({"tactic.default_tactic": "smt"}),
                lambda s: s["common"].update({"smt.nseq.monadic_leaf_budget": 1}),
                lambda s: s["common"].pop("smt.nseq.monadic_leaf"),
                lambda s: s["configurations"][1]["overrides"].clear(),
                lambda s: s["configurations"][1]["overrides"].update({"smt.nseq.abelian": True}),
                lambda s: s["configurations"][4]["overrides"].update(
                    {"smt.nseq.regex_factorization_threshold": False}),
                lambda s: s["configurations"].append({"name": "parikh", "overrides": {"smt.nseq.parikh": True}})):
            spec, _ = study.configurations()
            mutate(spec)
            with self.assertRaises(ValueError):
                study.validate_perf_matrix(spec)

    def historical_spec(self):
        return {"schema": 2, "baseline": "z3-tacas", "common": dict(study.DEFAULT_STUDY),
                "configurations": [{"name": n, "overrides": dict(v)}
                                   for n, v in study.DEFAULT_FLIPS.items()]}

    def test_historical_schema2_keeps_exact_seven_vectors(self):
        spec = self.historical_spec()
        with tempfile.TemporaryDirectory() as folder:
            path = Path(folder) / "old.json"
            study.write_json(path, spec)
            loaded, configs = study.configurations(path)
        self.assertEqual(spec, loaded)
        self.assertEqual(list(study.DEFAULT_FLIPS), list(configs))
        self.assertEqual(7, len(configs))
        self.assertIn("smt.nseq.equation_abstraction=false", configs["z3-tacas"])
        self.assertIn("smt.nseq.equation_abstraction=true", configs["z3-tacas-equation-abstraction"])
        self.assertIn("smt.nseq.monadic_leaf=false", configs["z3-tacas-no-monadic-leaf"])
        self.assertIn("smt.nseq.abelian=true", configs["z3-tacas-abelian"])

    def test_historical_schema_is_explicit_not_reinterpreted(self):
        spec = {"schema": 1, "baseline": "all-on", "common": {"smt.nseq.parikh": True},
                "groups": {"P": "smt.nseq.parikh_abstraction"},
                "configurations": [{"name": "all-on", "P": True}]}
        with tempfile.TemporaryDirectory() as tmp:
            path = Path(tmp) / "old.json"
            study.write_json(path, spec)
            loaded, configs = study.configurations(path)
        self.assertEqual(spec, loaded)
        self.assertEqual(["smt.nseq.parikh=true", "smt.nseq.parikh_abstraction=true"],
                         configs["all-on"])

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

    def test_new_schema_retains_all_files_including_token_duplicates(self):
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
            self.assertEqual(2, len(manifest["selected"]))
            self.assertEqual("a.smt2", manifest["selected"][0]["path"])
            self.assertEqual("", manifest["selected"][0]["expected"])
            self.assertEqual("sat", manifest["selected"][1]["expected"])
            historical = {"schema": 1, "baseline": "all-on", "common": {},
                          "groups": {"P": "smt.nseq.parikh_abstraction"},
                          "configurations": [{"name": "all-on", "P": True}]}
            old_config = Path(tmp) / "old.json"
            study.write_json(old_config, historical)
            old_plan = Path(tmp) / "old-plan"
            study.prepare(SimpleNamespace(corpus=root, corpus_sha=sha, out=old_plan,
                                          config=old_config, limit=None))
            old_manifest = json.loads((old_plan / "manifest.json").read_text())
            self.assertEqual(1, len(old_manifest["selected"]))
            self.assertEqual("sat", old_manifest["selected"][0]["expected"])

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

    def test_perf_error_policy_does_not_hide_invalid_models_or_corrupt_completeness(self):
        def row(config, status, verdicts, reason=""):
            return dict(id="0", repeat=0, config=config, status=status, seconds=1.0,
                        expected="", verdicts=verdicts, family="f", category="equations", reason=reason)
        baseline = row("TTTT", "sat", ["sat"])
        error = row("FTTT", "error", [], "crash")
        for schema in (1, 2, 3):
            summary = study.summarize([baseline, error], {}, ["TTTT", "FTTT"],
                                      "TTTT", 10, 2, schema=schema)
            self.assertEqual(schema == 3, summary["valid_for_comparison"])
            self.assertEqual(20, summary["paired"]["FTTT"]["par2_other_seconds"])
            self.assertEqual(1, len(summary["execution_errors"]))
        for message in ("an invalid model was generated", "model validation failed",
                        "failed to validate the model", "failed model validation",
                        "model-validation error"):
            status, reason, verdicts = study.parse_result(
                ('sat\n(error "' + message + '")').encode(), b"", -9, True, schema=3)
            self.assertEqual("invalid-model", status)
            invalid = row("FTTT", status, verdicts, reason)
            self.assertFalse(study.summarize([baseline, invalid], {}, ["TTTT", "FTTT"],
                                            "TTTT", 10, 2, schema=3)["valid_for_comparison"])
        for rows, count in (([baseline, row("FTTT", "unsat", ["unsat"])], 2),
                            ([baseline], 2), ([baseline, baseline], 2)):
            self.assertFalse(study.summarize(rows, {}, ["TTTT", "FTTT"], "TTTT", 10,
                                            count, schema=3)["valid_for_comparison"])
        wrong = row("FTTT", "unsat", ["unsat"])
        wrong["expected"] = "sat"
        self.assertFalse(study.summarize([wrong], {}, ["FTTT"], "FTTT", 10, 1,
                                        schema=3)["valid_for_comparison"])

    def test_perf_multiple_answers_are_fatal_not_tolerated_execution_errors(self):
        for output in (b"sat\nunsat", b"sat\nsat", b"unknown\nsat"):
            for stderr, code, killed in ((b"", 0, False), (b"error: failed", 0, False),
                                         (b"", -11, False), (b"", -9, True)):
                status, reason, verdicts = study.parse_result(
                    output, stderr, code, killed, schema=3)
                self.assertEqual("protocol-error", status)
                row = dict(id="0", repeat=0, config="TTTT", status=status, seconds=1.0,
                           expected="", verdicts=verdicts, family="f", category="equations",
                           reason=reason)
                summary = study.summarize([row], {}, ["TTTT"], "TTTT", 10, 1, schema=3)
                self.assertFalse(summary["valid_for_comparison"])
                self.assertEqual(1, summary["counts"]["TTTT"]["protocol-error"])
                self.assertEqual([], summary["execution_errors"])
                for schema in (1, 2):
                    self.assertEqual("error", study.parse_result(
                        output, stderr, code, killed, schema=schema)[0])

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
        spec = self.historical_spec()
        path = Path(tmp) / "historical.json"
        study.write_json(path, spec)
        _, configs = study.configurations(path)
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

    def make_perf_blocks(self, tmp, failure="error"):
        spec, configs = study.configurations()
        query = b"(assert true)\n(check-sat)\n"
        entry = dict(id="000000", path="f/a.smt2", family="f", category="equations", expected="",
                     sha256=study.digest(query), input_sha256=study.digest(query))
        manifest = dict(corpus="local", repository="local", fatal=[], selected=[entry])
        prefix = ["solver", "-t:10000", "-T:10", "-memory:512", "-st"]
        env = dict(platform="test", machine="x64", hostname="runner", processor="cpu",
                   cpu_count=8, timeout_seconds=10, memory_mb=512, memory_policy="allocator",
                   jobs=1, repeats=1, launch_prefix=prefix)
        record = dict(source_identity={"head": "a" * 40}, binary_sha256="b" * 64, build_evidence={})
        roots = [Path(tmp) / "first", Path(tmp) / "second"]
        names = list(configs)
        for root, arms in zip(roots, (names[:2], names[2:])):
            for folder in ("inputs", "original", "build-record", "raw/000000"):
                (root / folder).mkdir(parents=True)
            for folder in ("inputs", "original"):
                (root / folder / "000000.smt2").write_bytes(query)
            for name, value in (("manifest.json", manifest), ("configurations.json", spec),
                                ("environment.json", env), ("build-record/build.json", record)):
                study.write_json(root / name, value)
            rows = []
            for arm in arms:
                stdout = (b'(error "synthetic parser error")\n' if failure == "error" else
                          b'sat\n(error "an invalid model was generated")\n' if failure == "invalid-model"
                          else b"unsat\n") if arm == "FTTT" else b"sat\n"
                status, reason, verdicts = study.parse_result(stdout, b"", 0, schema=3)
                execution = dict(status=status, reason=reason, verdicts=verdicts, returncode=0,
                                 seconds=1.0, killed=False, statistics={},
                                 argv=prefix + configs[arm] + ["/recorded/inputs/000000.smt2"])
                raw = root / "raw" / "000000" / ("000-" + arm)
                raw.with_suffix(".stdout").write_bytes(stdout)
                raw.with_suffix(".stderr").write_bytes(b"")
                study.write_json(raw.with_suffix(".json"), execution)
                rows.append({**execution, **entry, "config": arm, "repeat": 0})
            (root / "runs.jsonl").write_text("".join(json.dumps(r) + "\n" for r in rows))
            study.write_json(root / "summary.json", study.summarize(
                rows, manifest, arms, spec["baseline"], 10, len(rows), schema=3))
            study.record_result_evidence(root)
        return roots

    def test_perf_merge_tolerates_errors_with_raw_integrity_and_PAR2_penalties(self):
        with tempfile.TemporaryDirectory() as folder:
            roots = self.make_perf_blocks(folder)
            out = Path(folder) / "merged"
            study.merge_results(SimpleNamespace(results=roots, out=out))
            summary = json.loads((out / "summary.json").read_text())
            self.assertTrue(summary["valid_for_comparison"])
            self.assertEqual(5, summary["completed_runs"])
            self.assertEqual(1, summary["counts"]["FTTT"]["error"])
            self.assertEqual(1, len(summary["execution_errors"]))
            self.assertEqual(20, summary["paired"]["FTTT"]["par2_other_seconds"])
            for label, selected in (("missing", roots[:1]), ("duplicate", roots + roots[:1])):
                with self.assertRaises(ValueError):
                    study.merge_results(SimpleNamespace(results=selected, out=Path(folder) / label))

    def test_perf_merge_rejects_models_contradictions_corruption_inputs_argv_and_source(self):
        for mode in ("invalid-model", "unsat", "corrupt", "input", "argv", "source"):
            with self.subTest(mode=mode), tempfile.TemporaryDirectory() as folder:
                roots = self.make_perf_blocks(folder, mode if mode in ("invalid-model", "unsat") else "error")
                root = roots[1]
                if mode == "corrupt":
                    next((root / "raw").rglob("*.stdout")).write_bytes(b"tampered")
                elif mode == "input":
                    (root / "inputs" / "000000.smt2").write_bytes(b"(check-sat)")
                    study.record_result_evidence(root)
                elif mode == "source":
                    path = root / "build-record" / "build.json"
                    record = json.loads(path.read_text())
                    record["binary_sha256"] = "c" * 64
                    study.write_json(path, record)
                    study.record_result_evidence(root)
                elif mode == "argv":
                    path = root / "runs.jsonl"
                    rows = [json.loads(line) for line in path.read_text().splitlines()]
                    rows[0]["argv"][3] = "-memory:1024"
                    path.write_text("".join(json.dumps(r) + "\n" for r in rows))
                    raw = root / "raw" / "000000" / ("000-" + rows[0]["config"] + ".json")
                    execution = json.loads(raw.read_text())
                    execution["argv"] = rows[0]["argv"]
                    study.write_json(raw, execution)
                    study.record_result_evidence(root)
                with self.assertRaises(ValueError):
                    study.merge_results(SimpleNamespace(results=roots, out=Path(folder) / "merged"))

    def test_merge_complete_configuration_blocks(self):
        with tempfile.TemporaryDirectory() as tmp:
            roots = self.make_blocks(tmp)
            out = Path(tmp) / "combined"
            study.merge_results(SimpleNamespace(results=roots, out=out))
            summary = json.loads((out / "summary.json").read_text())
            self.assertTrue(summary["valid_for_comparison"])
            self.assertEqual(7, summary["completed_runs"])
            self.assertEqual(6, len(summary["paired"]))
            self.assertEqual(1, summary["paired"]["z3-tacas-no-regex-parikh"]["jointly_decided_same_verdict"])
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
