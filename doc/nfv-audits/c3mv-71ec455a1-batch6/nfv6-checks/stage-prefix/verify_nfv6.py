"""One serialized, bounded validity attempt on the sealed P23 translation."""
import argparse
import hashlib
import json
import os
from pathlib import Path
import re
import shutil
import subprocess
import time
from datetime import datetime, timedelta, timezone


ROOT = Path(__file__).resolve().parent
CHECKS = ROOT / "nfv6-checks"


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def stable(text):
    code = re.sub(r"//[^\n]*", "", text)
    return "\n".join(line.strip() for line in code.splitlines() if line.strip() and not re.match(r"^\s*(assert|invariant|decreases)\b", line)) + "\n"


def validity_only(text, prop):
    first = text.index("method " + prop["entry_point"] + "(")
    last = text.index("\n{", first)
    rows = []
    removed = []
    for row in text[first:last].splitlines():
        match = re.fullmatch(r"\s*ensures (.+)", row)
        if match:
            assert rows and rows[-1].startswith("// synth:"), "Unrecognized contract annotation"
            rows.pop()
            removed.append(match[1])
        else:
            rows.append(row)
    assert removed == prop["original_ensures"], "Full frozen goal list must match before removal"
    result = text[:first] + "\n".join(rows) + text[last:]
    assert result[:first] == text[:first] and result.endswith(text[last:])
    old_requires = re.findall(r"^\s*requires (.+)$", text[first:last], re.M)
    new_requires = re.findall(r"^\s*requires (.+)$", result[first:result.index("\n{", first)], re.M)
    assert old_requires == new_requires == [c["clause"] for c in prop["assumptions"]]
    return result


def checked_annotations(candidate, canonical):
    code = re.sub(r"//[^\n]*", "", candidate)
    assert not re.search(r"\b(assume|expect|include|import|export|module|extern|abstract|opaque|iterator|yield|const|type|newtype|trait|codatatype)\b", code), "Forbidden trust/structural construct"
    assert "{:" not in code and not re.search(r"\bdecreases\s+\*", code), "Forbidden verifier escape"
    for row in code.splitlines():
        if re.match(r"\s*assert\b", row):
            assert re.fullmatch(r"\s*assert [^;{}]+;\s*", row), "Only a single checked assertion may occupy a proof line"
        elif re.match(r"\s*(invariant|decreases)\b", row):
            assert re.fullmatch(r"\s*(invariant|decreases) [^;{}]+", row), "Only a single proof clause may occupy a proof line"
    assert stable(candidate) == stable(canonical), "Computation/signatures/contracts/goals may not change"
    return candidate


def run_bounded(command,stream,wall_seconds):
    with subprocess.Popen(command,stdout=stream,stderr=subprocess.STDOUT) as process:
        try:
            return process.wait(timeout=wall_seconds),False,None
        except subprocess.TimeoutExpired:
            cleanup=(
                'function Stop-OwnedTree([int]$owned) { '
                'Get-CimInstance Win32_Process -Filter "ParentProcessId = $owned" | '
                'ForEach-Object { Stop-OwnedTree $_.ProcessId }; '
                'Stop-Process -Id $owned -Force -ErrorAction SilentlyContinue }; '
                'Stop-OwnedTree '+str(process.pid))
            subprocess.run(['powershell','-NoProfile','-NonInteractive','-Command',cleanup],
                check=True,stdout=subprocess.DEVNULL,stderr=subprocess.STDOUT,timeout=60)
            actual=process.wait(timeout=60)
            stream.write(('\n[audit harness] Wall-clock resource limit reached after '
                +str(wall_seconds)+' seconds; only this attempt process tree was stopped.\n').encode())
            stream.flush()
            return 124,True,actual


def load_sealed(root=ROOT):
    handoff = root / "nfv6-model-handoff.json"
    assert sha(handoff) == "bb7d679168d5196f1306adaa524023f3feb3d42eee2b5cea3616453ce35a2262"
    for name, digest in json.loads(handoff.read_text())["files"].items():
        assert sha(root.joinpath(*name.split("/"))) == digest, name
    freeze = json.loads((root / "nfv6-model-freeze.json").read_text())
    prop, = json.loads((root / "nfv6-models" / "properties.json").read_text())
    model_path = root / "nfv6-models" / "P23.dfy"
    assert sha(model_path) == prop["sha256"] == freeze["model_sha256"]
    model = model_path.read_text(encoding="utf-8")
    assert hashlib.sha256(stable(model).encode()).hexdigest() == freeze["non_proof_computation_contract_hash"]
    return model, prop


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--phase", required=True, choices=["validity"])
    parser.add_argument("--proof-candidate", type=Path)
    args = parser.parse_args()
    model, prop = load_sealed()
    CHECKS.mkdir(exist_ok=True)
    history_path = CHECKS / "checks.json"
    history = json.loads(history_path.read_text()) if history_path.exists() else []
    for row in history:
        assert sha(CHECKS / row["input"]) == row["input_sha256"]
        assert sha(CHECKS / row["log"]) == row["raw_log_sha256"]
    candidate_path = None
    candidate_sha = prop["sha256"]
    if args.proof_candidate is not None:
        candidate_path = args.proof_candidate.resolve()
        assert candidate_path.is_relative_to(ROOT), "Candidate must be an explicit session artifact"
        annotated = checked_annotations(candidate_path.read_text(encoding="utf-8"), model)
        candidate_sha = sha(candidate_path)
    else:
        annotated = model
    prefix_path = CHECKS / "stage-initial" / "checks-prefix.json"
    if prefix_path.exists():
        prefix = json.loads(prefix_path.read_text())
        assert history[:len(prefix)] == prefix, "Historical attempt prefix changed"
    text = validity_only(annotated, prop)
    digest = hashlib.sha256(text.encode()).hexdigest()
    assert not any(h["kind"] == args.phase and h["input_sha256"] == digest for h in history), "Identical attempt already retained; no silent repeats"
    sequence = len(history) + 1
    stem = f"{sequence:03}-P23-{args.phase}"
    path = CHECKS / (stem + ".dfy")
    log = CHECKS / (stem + ".log")
    receipt = CHECKS / (stem + ".start.json")
    snapshot = CHECKS / (stem + ".runner.py")
    lock = CHECKS / ".running"
    command = [str(ROOT / "nfv-tools" / "dafny" / "Dafny.exe"), "verify", str(path), "--solver-path", str(ROOT / "nfv-tools" / "dafny" / "z3" / "bin" / "z3-4.12.1.exe"), "--verification-time-limit", "30", "--cores", "2", "--allow-warnings", "--show-snippets", "false", "--progress", "Symbol"]
    started = datetime.now(timezone.utc)
    active = {"runner_pid": os.getpid(), "sequence": sequence, "kind": args.phase, "started_utc": started.isoformat(), "wall_deadline_utc": (started + timedelta(seconds=600)).isoformat(), "input": path.name, "command": command, "canonical_sha256": prop["sha256"], "input_sha256": digest, "removed_ensures": prop["original_ensures"], "retained_entry_requires": [r["clause"] for r in prop["assumptions"]], "retained_helpers": len(prop["environment"]), "wall_seconds": 600, "mbqi_override": False, "isolate_assertions": False}
    active["full_goal_candidate"] = candidate_path.relative_to(ROOT).as_posix() if candidate_path else None
    active["full_goal_candidate_sha256"] = candidate_sha
    with lock.open("x", encoding="utf-8") as out:
        json.dump(active, out, indent=2)
        out.write("\n")
    try:
        for item in [path, log, receipt, snapshot]:
            assert not item.exists(), item
        path.write_text(text, encoding="utf-8", newline="\n")
        assert sha(path) == digest
        shutil.copyfile(Path(__file__), snapshot)
        receipt.write_text(json.dumps({**active, "runner_sha256": sha(snapshot)}, indent=2) + "\n", encoding="utf-8", newline="\n")
        print(json.dumps({"status": "started validity ONLY", "runner_pid": os.getpid(), "sequence": sequence, "deadline_utc": active["wall_deadline_utc"], "input_sha256": digest}), flush=True)
        before = time.monotonic()
        with log.open("xb") as stream:
            exit_code, timed_out, actual_exit = run_bounded(command, stream, 600)
        raw = log.read_bytes()
        output = raw.decode("utf-8-sig", errors="replace")
        summary = re.search(r"Dafny program verifier finished with (\d+) verified, (\d+) errors?", output)
        admitted = exit_code == 0 and not timed_out and summary is not None and int(summary[1]) > 0 and int(summary[2]) == 0
        record = {**active, "seconds": round(time.monotonic() - before, 3), "exit_code": exit_code, "wall_timed_out": timed_out, "interrupted_process_exit_code": actual_exit, "input_sha256": sha(path), "log": log.name, "raw_log_sha256": sha(log), "runner": snapshot.name, "runner_sha256": sha(snapshot), "admitted": admitted, "internal_obligations_verified": int(summary[1]) if summary else None, "diagnostic_errors": int(summary[2]) if summary else None, "scope": "property-free validity ONLY; no concrete domains or complete positive property checked", "native_executions": 0}
        history.append(record)
        temporary = CHECKS / "checks.json.next"
        assert not temporary.exists()
        temporary.write_text(json.dumps(history, indent=2) + "\n", encoding="utf-8", newline="\n")
        temporary.replace(history_path)
        result = CHECKS / (stem + ".result.json")
        with result.open("x", encoding="utf-8") as out:
            json.dump(record, out, indent=2)
            out.write("\n")
        print(json.dumps({"sequence": sequence, "kind": args.phase, "seconds": record["seconds"], "exit_code": exit_code, "admitted": admitted, "wall_timed_out": timed_out}), flush=True)
        print("\n".join(output.splitlines()[-24:]), flush=True)
    finally:
        lock.unlink()
    return 0 if admitted else 1


if __name__ == "__main__":
    raise SystemExit(main())
