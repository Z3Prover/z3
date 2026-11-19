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
    model, prop = runner.load_sealed()
    checks = ROOT / "nfv6-checks"
    assert not (checks / ".running").exists()
    history = json.loads((checks / "checks.json").read_text())
    record, = history
    assert record["sequence"] == 1 and record["kind"] == "validity"
    assert record["exit_code"] == 4 and record["admitted"] is False
    assert not record["wall_timed_out"] and record["interrupted_process_exit_code"] is None
    assert record["internal_obligations_verified"] == 31 and record["diagnostic_errors"] == 2
    assert record["removed_ensures"] == prop["original_ensures"]
    assert record["retained_entry_requires"] == [c["clause"] for c in prop["assumptions"]]
    checked = checks / record["input"]
    assert sha(checked) == record["input_sha256"]
    assert checked.read_bytes() == runner.validity_only(model, prop).encode()
    for key, hash_key in [("log", "raw_log_sha256"), ("runner", "runner_sha256")]:
        assert sha(checks / record[key]) == record[hash_key]
    checked_lines = checked.read_text().splitlines()
    raw_log = (checks / record["log"]).read_text()
    diagnostics = [{"line": int(n), "column": int(c), "message": message, "checked_annotation": checked_lines[int(n) - 1].strip()} for n, c, message in re.findall(r"\((\d+),(\d+)\): Error: ([^\r\n]+)", raw_log)]
    assert len(diagnostics) == 2
    assert diagnostics[0]["checked_annotation"].startswith("invariant used ==")
    assert diagnostics[1]["checked_annotation"].startswith("assert CountLowDigits")
    snapshots = checks / "stage-initial"
    assert not snapshots.exists()
    snapshots.mkdir()
    shutil.copyfile(checks / "checks.json", snapshots / "checks-prefix.json")
    for name in ["verify_nfv6.py", "test_nfv6_runner.py", "verify_nfv5.py", "test_nfv5_watchdog.py"]:
        shutil.copyfile(ROOT / name, snapshots / name)
    files = {
        name: sha(ROOT / name) for name in [
            "nfv6-validity-initial.md", "finalize_nfv6_validity_initial.py",
            "nfv6-runner-tests.log", "nfv6-runner-tests.json",
            "nfv6-runner-exit-tests.log", "nfv6-runner-exit-tests.json",
            "nfv6-model-handoff.json",
        ]
    }
    for path in checks.iterdir():
        if path.is_file() and path.name != "checks.json":
            files[path.relative_to(ROOT).as_posix()] = sha(path)
    for path in snapshots.iterdir():
        files[path.relative_to(ROOT).as_posix()] = sha(path)
    assert subprocess.check_output(["git", "branch", "--show-current"], cwd=REPO).strip() == b"c3mv"
    assert subprocess.check_output(["git", "rev-parse", "HEAD"], cwd=REPO).strip() == b"4be813a75bdc59574df23da8ce5805a262171ba9"
    assert subprocess.check_output(["git", "rev-parse", "refs/stash"], cwd=REPO).strip() == b"7af7fad70e9cea38601c67ff00d89f6b5576c2d6"
    assert not subprocess.check_output(["git", "--no-pager", "status", "--porcelain=v1", "-uall"], cwd=REPO)
    result = {
        "stage": "nfv6-verify", "status": "initial validity attempt complete; gate NOT admitted",
        "files": files, "checked_input_sha256": record["input_sha256"],
        "verifier_attempts": 1, "verifier_exit": 4, "seconds": record["seconds"],
        "internal_obligations_verified": 31, "unproved_annotations": diagnostics,
        "wall_timed_out": False, "resource_intervention": False,
        "whole_properties_verified": 0, "whole_properties_refuted": 0,
        "domain_attempts": 0, "original_positive_attempts": 0, "native_executions": 0,
        "first_wrapper_exit": 0,
        "first_wrapper_exit_note": "Historical wrapper process succeeded in recording Dafny exit4/admittedfalse; corrected current wrapper now returns1 on gate failure. Exact old runner retained, correction tested without another SMT invocation.",
        "history_policy": "Mutable nfv6-checks/checks.json excluded from this seal. Immutable checks-prefix.json captures exactly the first record; later attempts may ONLY append, preserving this prefix and every first-attempt byte.",
        "tool_policy": "Current runner/test files may be extended later; this stage seals exact immutable snapshots, not their future mutable working paths.",
        "next_stage": "nfv6-validity-hints", "schedule_id": 2, "stop_schedule": False,
    }
    out = ROOT / "nfv6-validity-initial-handoff.json"
    assert not out.exists()
    out.write_text(json.dumps(result, indent=2) + "\n", encoding="utf-8", newline="\n")
    for name, digest in files.items():
        assert sha(ROOT.joinpath(*name.split("/"))) == digest
    print(json.dumps({"status": result["status"], "attempts": 1, "verified_internal": 31, "unproved_annotations": diagnostics, "handoff_sha256": sha(out), "files_sealed": len(files), "next_stage": result["next_stage"]}, indent=2))


if __name__ == "__main__":
    main()
