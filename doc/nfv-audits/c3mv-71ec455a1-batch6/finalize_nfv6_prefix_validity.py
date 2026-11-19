import hashlib
import json
from pathlib import Path
import shutil
import subprocess

import verify_nfv6 as runner


ROOT = Path(__file__).resolve().parent
REPO = Path(r"C:\z3seq")


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def main():
    for name, digest in [("nfv6-model-handoff.json", "bb7d679168d5196f1306adaa524023f3feb3d42eee2b5cea3616453ce35a2262"), ("nfv6-validity-initial-handoff.json", "5bf889f2a50189cdf52b0c999a529a335d462dd5c874f90193207bc0fab3b9f0")]:
        assert sha(ROOT / name) == digest
        for child, value in json.loads((ROOT / name).read_text())["files"].items():
            assert sha(ROOT.joinpath(*child.split("/"))) == value, child
    canonical, prop = runner.load_sealed()
    candidate_dir = ROOT / "nfv6-proof-hints" / "001-prefix"
    candidate_path = candidate_dir / "P23.dfy"
    assert sha(candidate_path) == "417aabd6217094188bd7d02d3aa43e3372e35ee587a52ebbb5f3460409bdc074"
    candidate = runner.checked_annotations(candidate_path.read_text(), canonical)
    checks = ROOT / "nfv6-checks"
    assert not (checks / ".running").exists()
    history = json.loads((checks / "checks.json").read_text())
    prefix = json.loads((checks / "stage-initial" / "checks-prefix.json").read_text())
    assert len(history) == 2 and history[:len(prefix)] == prefix
    current = history[1]
    assert current["sequence"] == 2 and current["kind"] == "validity" and current["admitted"]
    assert current["exit_code"] == 0 and not current["wall_timed_out"]
    assert current["internal_obligations_verified"] == 32 and current["diagnostic_errors"] == 0
    assert current["full_goal_candidate_sha256"] == sha(candidate_path)
    assert current["removed_ensures"] == prop["original_ensures"]
    assert current["retained_entry_requires"] == [c["clause"] for c in prop["assumptions"]]
    assert (checks / current["input"]).read_bytes() == runner.validity_only(candidate, prop).encode()
    for record in history:
        for name, digest in [(record["input"], record["input_sha256"]), (record["log"], record["raw_log_sha256"]), (record["runner"], record["runner_sha256"])]:
            assert sha(checks / name) == digest
    snapshots = checks / "stage-prefix"
    assert not snapshots.exists()
    snapshots.mkdir()
    shutil.copyfile(checks / "checks.json", snapshots / "checks-prefix.json")
    for name in ["verify_nfv6.py", "test_nfv6_runner.py", "prepare_nfv6_prefix_hints.py"]:
        shutil.copyfile(ROOT / name, snapshots / name)
    files = {name: sha(ROOT / name) for name in ["nfv6-model-handoff.json", "nfv6-validity-initial-handoff.json", "nfv6-validity-hints.md", "finalize_nfv6_prefix_validity.py", "nfv6-prefix-runner-tests.json", "nfv6-prefix-runner-tests.log"]}
    for directory in [candidate_dir, snapshots]:
        for path in directory.iterdir():
            assert path.is_file()
            files[path.relative_to(ROOT).as_posix()] = sha(path)
    for path in checks.glob("002-*"):
        files[path.relative_to(ROOT).as_posix()] = sha(path)
    assert json.loads((ROOT / "nfv6-prefix-runner-tests.json").read_text())["tests_run"] == 6
    assert json.loads((ROOT / "nfv6-prefix-runner-tests.json").read_text())["status"] == "pass"
    assert subprocess.check_output(["git", "branch", "--show-current"], cwd=REPO).strip() == b"c3mv"
    assert subprocess.check_output(["git", "rev-parse", "HEAD"], cwd=REPO).strip() == b"4be813a75bdc59574df23da8ce5805a262171ba9"
    assert subprocess.check_output(["git", "rev-parse", "refs/stash"], cwd=REPO).strip() == b"7af7fad70e9cea38601c67ff00d89f6b5576c2d6"
    assert not subprocess.check_output(["git", "--no-pager", "status", "--porcelain=v1", "-uall"], cwd=REPO)
    result = {
        "stage": "nfv6-validity-hints", "status": "property-free validity ADMITTED; original semantic property NOT checked",
        "files": files, "total_verifier_attempts": 2, "this_stage_verifier_attempts": 1,
        "validity_sequence": 2, "validity_input_sha256": current["input_sha256"],
        "admitted_full_goal_candidate": candidate_path.relative_to(ROOT).as_posix(),
        "admitted_full_goal_candidate_sha256": sha(candidate_path),
        "canonical_model_sha256": prop["sha256"],
        "non_proof_computation_contract_hash": hashlib.sha256(runner.stable(candidate).encode()).hexdigest(),
        "seconds": current["seconds"], "verifier_exit": 0, "internal_obligations_verified": 32,
        "this_stage_tooling_tests": 6, "added_checked_assertions": 10,
        "domain_attempts": 0, "original_positive_attempts": 0, "refutation_attempts": 0,
        "whole_properties_verified": 0, "whole_properties_refuted": 0, "native_executions": 0,
        "history_policy": "Only append to global checks.json preserving this sealed two-record prefix; never modify earlier checked bytes",
        "next_stage": "nfv6-domain", "schedule_id": 2, "stop_schedule": False,
    }
    path = ROOT / "nfv6-validity-hints-handoff.json"
    assert not path.exists()
    path.write_text(json.dumps(result, indent=2) + "\n", encoding="utf-8", newline="\n")
    print(json.dumps({"status": result["status"], "attempts": 2, "internal_verified": 32, "full_goal_candidate_sha256": sha(candidate_path), "handoff_sha256": sha(path), "sealed_files": len(files), "next_stage": result["next_stage"]}, indent=2))


if __name__ == "__main__":
    main()
