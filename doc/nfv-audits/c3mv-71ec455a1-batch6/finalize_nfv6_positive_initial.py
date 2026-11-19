import hashlib
import json
from pathlib import Path
import re
import shutil
import subprocess

import verify_nfv6 as runner


ROOT = Path(__file__).resolve().parent
REPO = Path(r"C:\z3seq")


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def main():
    for name, digest in [("nfv6-domain-handoff.json", "55c9bb9327cbd9ca46f3a440ab5b7668e91498a3f56052965f0d26f052584fcc"), ("nfv6-validity-hints-handoff.json", "68384b907449ca5e3ee7998b891d39caf7dd2a71cfe4e0eab1300371fb1aa032"), ("nfv6-model-handoff.json", "bb7d679168d5196f1306adaa524023f3feb3d42eee2b5cea3616453ce35a2262"), ("nfv6-validity-initial-handoff.json", "5bf889f2a50189cdf52b0c999a529a335d462dd5c874f90193207bc0fab3b9f0")]:
        assert sha(ROOT / name) == digest
        for child, value in json.loads((ROOT / name).read_text())["files"].items():
            path = ROOT.joinpath(*child.split("/"))
            assert sha(path) == value, child
    canonical, prop = runner.load_sealed()
    candidate_path = ROOT / "nfv6-proof-hints" / "001-prefix" / "P23.dfy"
    candidate = runner.checked_annotations(candidate_path.read_text(), canonical)
    runner.original_positive(candidate, prop)
    checks = ROOT / "nfv6-checks"
    assert not (checks / ".running").exists()
    history = json.loads((checks / "checks.json").read_text())
    prefix = json.loads((checks / "stage-domain" / "checks-prefix.json").read_text())
    assert len(history) == 4 and history[:len(prefix)] == prefix
    current = history[3]
    assert current["kind"] == "proof" and current["sequence"] == 4 and not current["admitted"]
    assert current["exit_code"] == 4 and not current["wall_timed_out"]
    assert current["internal_obligations_verified"] == 32 and current["diagnostic_errors"] == 3
    assert current["gate_validity_sequence"] == 2 and current["gate_domain_sequence"] == 3
    assert current["removed_ensures"] == [] and current["checked_original_ensures"] == prop["original_ensures"]
    assert not current["whole_property_verified"] and not current["whole_property_refuted"]
    assert (checks / current["input"]).read_bytes() == candidate.encode()
    assert current["input_sha256"] == sha(candidate_path)
    for record in history:
        for name, digest in [(record["input"], record["input_sha256"]), (record["log"], record["raw_log_sha256"]), (record["runner"], record["runner_sha256"])]:
            assert sha(checks / name) == digest
    lines = (checks / current["input"]).read_text().splitlines()
    raw_log = (checks / current["log"]).read_text()
    assert not re.search(r"timed out|time outs?", raw_log, re.I)
    diagnostics = [{"line": int(n), "column": int(c), "kind": kind, "message": message, "checked_text": lines[int(n) - 1].strip()} for n, c, kind, message in re.findall(r"\((\d+),(\d+)\): (Error|Related location): ([^\r\n]+)", raw_log)]
    assert len(diagnostics) == 6 and sum(d["kind"] == "Error" for d in diagnostics) == 3
    native_path = REPO / "src" / "ast" / "simplifiers" / "seq_regular_simplifier.cpp"
    native_lines = native_path.read_text().splitlines()
    model_lines = canonical.splitlines()
    assert native_lines[284].strip() == "return keep(u.re.mk_range(empty->get_sort(), '0' + lo, '0' + hi));"
    assert model_lines[271].strip() == "0 <= i < |word| && j == i + 1 && lo <= word[i] <= hi"
    assert model_lines[339].strip() == "seq(Width(word) * Width(word), k => RangeAt(word, lo, hi, k / Width(word), k % Width(word)))"
    assert "  language := MRange(lo, hi, word);" in model_lines
    assert "  if n < 0 then [] else if n < 10 then [48 + n] else Digits(n / 10) + [48 + n % 10]" in model_lines
    contrasts = [{"lo": lo, "hi": hi, "character_code": code, "frozen_helper_predicate": lo <= code <= hi, "source_declared_ascii_predicate": 48 + lo <= code <= 48 + hi} for lo, hi, code in [(0, 9, 48), (0, 9, 0), (1, 9, 49)]]
    assert all(c["frozen_helper_predicate"] != c["source_declared_ascii_predicate"] for c in contrasts)
    correspondence = {
        "classification": "confirmed model translation/source-correspondence failure; NOT a C++ bug",
        "source_pin": "71ec455a18702fe695d0c924a535ff9f385bd58d",
        "source_file": "src/ast/simplifiers/seq_regular_simplifier.cpp",
        "source_line": 285, "source_text": native_lines[284],
        "canonical_model_sha256": prop["sha256"],
        "model_source": "nfv6-models/P23.dfy",
        "model_lines": {"RangeAt": 272, "MRange": 340},
        "model_text": [model_lines[271], model_lines[339]],
        "arithmetic_contrasts": contrasts,
        "contrasts_scope": "closed-form helper predicate comparison only; not native execution or formal whole-property counterexamples",
        "sealed_model_changed": False, "source_correctness_admitted": False,
        "next_action": "Publish preserved batch6 audit failure; separately pre-freeze same-intent corrected retranslation with fresh gates and zero new source coverage",
    }
    correspondence_path = ROOT / "nfv6-correspondence-failure.json"
    assert not correspondence_path.exists()
    snapshots = checks / "stage-positive-initial"
    assert not snapshots.exists()
    snapshots.mkdir()
    shutil.copyfile(checks / "checks.json", snapshots / "checks-prefix.json")
    for name in ["verify_nfv6.py", "test_nfv6_runner.py"]:
        shutil.copyfile(ROOT / name, snapshots / name)
    files = {name: sha(ROOT / name) for name in ["nfv6-positive-initial.md", "finalize_nfv6_positive_initial.py", "nfv6-positive-runner-tests.log", "nfv6-positive-runner-tests.json", "nfv6-domain-handoff.json", "nfv6-model-handoff.json"]}
    for path in snapshots.iterdir():
        files[path.relative_to(ROOT).as_posix()] = sha(path)
    for path in checks.glob("004-*"):
        files[path.relative_to(ROOT).as_posix()] = sha(path)
    tests = json.loads((ROOT / "nfv6-positive-runner-tests.json").read_text())
    assert tests["status"] == "pass" and tests["tests_run"] == 13
    assert subprocess.check_output(["git", "branch", "--show-current"], cwd=REPO).strip() == b"c3mv"
    assert subprocess.check_output(["git", "rev-parse", "HEAD"], cwd=REPO).strip() == b"4be813a75bdc59574df23da8ce5805a262171ba9"
    assert subprocess.check_output(["git", "rev-parse", "refs/stash"], cwd=REPO).strip() == b"7af7fad70e9cea38601c67ff00d89f6b5576c2d6"
    assert not subprocess.check_output(["git", "--no-pager", "status", "--porcelain=v1", "-uall"], cwd=REPO)
    correspondence_path.write_text(json.dumps(correspondence, indent=2) + "\n", encoding="utf-8", newline="\n")
    files[correspondence_path.name] = sha(correspondence_path)
    result = {
        "stage": "nfv6-positive", "status": "complete original positive NOT proved/NOT refuted; confirmed source-correspondence audit failure",
        "files": files, "total_verifier_attempts": 4, "this_stage_verifier_attempts": 1,
        "positive_sequence": 4, "positive_input_sha256": current["input_sha256"],
        "validity_sequence": 2, "domain_sequence": 3, "literal_domains_admitted": 16,
        "original_ensures_checked_together": prop["original_ensures"],
        "canonical_model_sha256": prop["sha256"],
        "non_proof_computation_contract_hash": hashlib.sha256(runner.stable(candidate).encode()).hexdigest(),
        "seconds": current["seconds"], "verifier_exit": 4, "internal_obligations_verified": 32,
        "diagnostic_errors": 3, "diagnostics": diagnostics, "reported_timeouts": 0,
        "watchdog_interventions": 0, "tooling_tests": 13, "refutation_attempts": 0,
        "whole_properties_verified": 0, "whole_properties_refuted": 0, "native_executions": 0,
        "history_policy": "Only append to global checks.json preserving this sealed four-record prefix; every earlier checked byte stays immutable",
        "source_correspondence_admitted": False, "model_translation_failures": 1,
        "assertion_isolated_followup_cancelled_before_execution": True,
        "new_source_coverage_claims": 0,
        "next_stage": "nfv6-results", "schedule_id": 2, "stop_schedule": False,
    }
    path = ROOT / "nfv6-positive-initial-handoff.json"
    assert not path.exists()
    path.write_text(json.dumps(result, indent=2) + "\n", encoding="utf-8", newline="\n")
    print(json.dumps({"status": result["status"], "attempts": 4, "internal_verified": 32, "diagnostic_errors": 3, "handoff_sha256": sha(path), "sealed_files": len(files), "next_stage": result["next_stage"]}, indent=2))


if __name__ == "__main__":
    main()
