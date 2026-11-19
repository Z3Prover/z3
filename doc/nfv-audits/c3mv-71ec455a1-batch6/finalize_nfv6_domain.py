import ast
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
    for name, digest in [("nfv6-validity-hints-handoff.json", "68384b907449ca5e3ee7998b891d39caf7dd2a71cfe4e0eab1300371fb1aa032"), ("nfv6-model-handoff.json", "bb7d679168d5196f1306adaa524023f3feb3d42eee2b5cea3616453ce35a2262"), ("nfv6-validity-initial-handoff.json", "5bf889f2a50189cdf52b0c999a529a335d462dd5c874f90193207bc0fab3b9f0")]:
        assert sha(ROOT / name) == digest
        for child, value in json.loads((ROOT / name).read_text())["files"].items():
            path = ROOT.joinpath(*child.split("/"))
            assert sha(path) == value, child
    canonical, prop = runner.load_sealed()
    candidate_path = ROOT / "nfv6-proof-hints" / "001-prefix" / "P23.dfy"
    candidate = runner.checked_annotations(candidate_path.read_text(), canonical)
    checks = ROOT / "nfv6-checks"
    assert not (checks / ".running").exists()
    history = json.loads((checks / "checks.json").read_text())
    prefix = json.loads((checks / "stage-prefix" / "checks-prefix.json").read_text())
    assert len(history) == 3 and history[:len(prefix)] == prefix
    current = history[2]
    assert current["kind"] == "domain" and current["sequence"] == 3 and current["admitted"]
    assert current["exit_code"] == 0 and not current["wall_timed_out"]
    assert current["internal_obligations_verified"] == 48 and current["diagnostic_errors"] == 0
    assert current["gate_validity_sequence"] == 2
    assert current["domain_example_ids"] == [e["id"] for e in prop["witnesses"]]
    assert len(current["domain_example_ids"]) == 16
    for record in history:
        for name, digest in [(record["input"], record["input_sha256"]), (record["log"], record["raw_log_sha256"]), (record["runner"], record["runner_sha256"])]:
            assert sha(checks / name) == digest
    validity = runner.validity_only(candidate, prop)
    assert hashlib.sha256(validity.encode()).hexdigest() == history[1]["input_sha256"]
    checked = (checks / current["input"]).read_text()
    assert checked == runner.domain_callers(validity, prop)
    callers = re.findall(r"method ConcreteDomain(\d+)\(\)\n\{\n(.*?)\n\}", checked[len(validity):], re.S)
    assert [int(n) for n, body in callers] == list(range(1, 17))
    for (_, body), example in zip(callers, prop["witnesses"], strict=True):
        assertions = [line.strip()[7:-1] for line in body.splitlines() if line.strip().startswith("assert ")]
        assert assertions == [c["clause"] for c in prop["assumptions"]]
        assert "ensures " not in body and "assume " not in body
        for item in prop["inputs"]:
            lead = "  var " + item["name"] + ": " + item["type"] + " := "
            row, = [line for line in body.splitlines() if line.startswith(lead)]
            value = ast.literal_eval(row[len(lead):-1].replace("true", "True").replace("false", "False"))
            assert value == example["inputs"][item["name"]]
        calls = re.findall(r"var (out[0-9]+(?:,\s*out[0-9]+)*) := DecimalGreater\(([^)]+)\);", body)
        assert len(calls) == 1
        outputs, args = calls[0]
        assert [x.strip() for x in outputs.split(",")] == ["out0", "out1", "out2", "out3"]
        assert [x.strip() for x in args.split(",")] == [item["name"] for item in prop["inputs"]]
    snapshots = checks / "stage-domain"
    assert not snapshots.exists()
    snapshots.mkdir()
    shutil.copyfile(checks / "checks.json", snapshots / "checks-prefix.json")
    for name in ["verify_nfv6.py", "test_nfv6_runner.py"]:
        shutil.copyfile(ROOT / name, snapshots / name)
    files = {name: sha(ROOT / name) for name in ["nfv6-domain.md", "finalize_nfv6_domain.py", "nfv6-domain-runner-tests.log", "nfv6-domain-runner-tests.json", "nfv6-validity-hints-handoff.json", "nfv6-model-handoff.json"]}
    for path in snapshots.iterdir():
        files[path.relative_to(ROOT).as_posix()] = sha(path)
    for path in checks.glob("003-*"):
        files[path.relative_to(ROOT).as_posix()] = sha(path)
    for path in (ROOT / "nfv6-tool-attempts" / "001-domain-finalizer").iterdir():
        files[path.relative_to(ROOT).as_posix()] = sha(path)
    tests = json.loads((ROOT / "nfv6-domain-runner-tests.json").read_text())
    assert tests["status"] == "pass" and tests["tests_run"] == 10
    assert subprocess.check_output(["git", "branch", "--show-current"], cwd=REPO).strip() == b"c3mv"
    assert subprocess.check_output(["git", "rev-parse", "HEAD"], cwd=REPO).strip() == b"4be813a75bdc59574df23da8ce5805a262171ba9"
    assert subprocess.check_output(["git", "rev-parse", "refs/stash"], cwd=REPO).strip() == b"7af7fad70e9cea38601c67ff00d89f6b5576c2d6"
    assert not subprocess.check_output(["git", "--no-pager", "status", "--porcelain=v1", "-uall"], cwd=REPO)
    result = {
        "stage": "nfv6-domain", "status": "all16 independent concrete domains ADMITTED; original semantic property NOT checked",
        "files": files, "total_verifier_attempts": 3, "this_stage_verifier_attempts": 1,
        "domain_sequence": 3, "domain_input_sha256": current["input_sha256"],
        "validity_sequence": 2, "validity_input_sha256": history[1]["input_sha256"],
        "admitted_full_goal_candidate": candidate_path.relative_to(ROOT).as_posix(),
        "admitted_full_goal_candidate_sha256": sha(candidate_path),
        "canonical_model_sha256": prop["sha256"],
        "non_proof_computation_contract_hash": hashlib.sha256(runner.stable(candidate).encode()).hexdigest(),
        "seconds": current["seconds"], "verifier_exit": 0, "internal_obligations_verified": 48,
        "literal_examples_admitted": 16, "all_inputs_bound_per_caller": 5,
        "entry_requires_asserted_per_caller": 4, "outputs_per_call": 4,
        "original_positive_postconditions_borrowed": 0, "expected_output_assumptions": 0,
        "tooling_tests": 10, "original_positive_attempts": 0, "refutation_attempts": 0,
        "whole_properties_verified": 0, "whole_properties_refuted": 0, "native_executions": 0,
        "history_policy": "Only append to global checks.json preserving this sealed three-record prefix; every earlier input/log/runner/receipt remains immutable",
        "next_stage": "nfv6-positive", "schedule_id": 2, "stop_schedule": False,
    }
    path = ROOT / "nfv6-domain-handoff.json"
    assert not path.exists()
    path.write_text(json.dumps(result, indent=2) + "\n", encoding="utf-8", newline="\n")
    print(json.dumps({"status": result["status"], "attempts": 3, "internal_verified": 48, "domain_callers": 16, "domain_input_sha256": current["input_sha256"], "handoff_sha256": sha(path), "sealed_files": len(files), "next_stage": result["next_stage"]}, indent=2))


if __name__ == "__main__":
    main()
