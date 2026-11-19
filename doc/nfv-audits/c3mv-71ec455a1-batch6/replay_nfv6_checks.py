"""Explicit, bounded historical replay of an audit-failed model, never a repair."""
import argparse
import json
from pathlib import Path
import re
import sys
import time

sys.dont_write_bytecode = True

import verify_nfv6 as runner
from validate_nfv6_publication import validate


def replay_command(record, input_path, dafny, solver):
    command = list(record["command"])
    assert command[1] == "verify" and command.count("--solver-path") == 1
    assert Path(solver).name.lower() == "z3-4.12.1.exe", "Select the explicitly pinned solver"
    command[0], command[2] = str(dafny), str(input_path)
    command[command.index("--solver-path") + 1] = str(solver)
    return command


def replay(root, sequence, dafny, solver, out, acknowledge=False):
    if not acknowledge:
        raise PermissionError("Explicit acknowledgement of the model audit failure is required")
    root, out = root.resolve(), out.resolve()
    if out.is_relative_to(root) or out.exists():
        raise ValueError("Replay output must be a NEW directory outside the immutable bundle")
    validate(root)
    assert dafny.is_file() and solver.is_file(), "Supply the official external verifier and pinned solver"
    rows = json.loads((root / "nfv6-checks" / "checks.json").read_text())
    record, = [r for r in rows if r["sequence"] == sequence]
    input_path = out / record["input"]
    command = replay_command(record, input_path, dafny, solver)
    out.mkdir(parents=True)
    input_path.write_bytes((root / "nfv6-checks" / record["input"]).read_bytes())
    assert runner.sha(input_path) == record["input_sha256"]
    (out / "start.json").write_text(json.dumps({"historical_sequence": sequence, "command": command, "input_sha256": record["input_sha256"], "wall_seconds": 600, "model_correspondence_failed": True}, indent=2) + "\n", encoding="utf-8", newline="\n")
    before = time.monotonic()
    log_path = out / "replay.log"
    with log_path.open("xb") as stream:
        code, timed_out, actual_exit = runner.run_bounded(command, stream, 600)
    text = log_path.read_text(encoding="utf-8-sig", errors="replace")
    summary = re.search(r"Dafny program verifier finished with (\d+) verified, (\d+) errors?", text)
    result = {"historical_sequence": sequence, "exit_code": code, "wall_timed_out": timed_out, "interrupted_process_exit_code": actual_exit, "seconds": round(time.monotonic() - before, 3), "log_sha256": runner.sha(log_path), "internal_verified": int(summary[1]) if summary else None, "diagnostic_errors": int(summary[2]) if summary else None, "historical_exit": record["exit_code"], "exit_matches_history": code == record["exit_code"], "source_correctness_admitted": False, "native_executions": 0}
    (out / "result.json").write_text(json.dumps(result, indent=2) + "\n", encoding="utf-8", newline="\n")
    return result


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--sequence", type=int, required=True, choices=[1, 2, 3, 4])
    parser.add_argument("--dafny", type=Path, required=True)
    parser.add_argument("--solver", type=Path, required=True)
    parser.add_argument("--out", type=Path, required=True)
    parser.add_argument("--acknowledge-audit-failure", action="store_true")
    args = parser.parse_args()
    print(json.dumps(replay(Path(__file__).resolve().parent, args.sequence, args.dafny, args.solver, args.out, args.acknowledge_audit_failure), indent=2))
