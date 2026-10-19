#!/usr/bin/env python3
"""Compare Z3 QSAT and the CAV 2026 MuCyc artifact on quantified SMT inputs."""

import argparse
from collections import Counter, defaultdict
from datetime import datetime, timezone
import hashlib
import json
import math
import os
from pathlib import Path
import platform
import re
import signal
import subprocess
import threading
import time

SPACE = r"(?:\s|;[^\n]*(?:\n|$))*"


def sha256(path):
    with path.open("rb") as stream:
        return hashlib.file_digest(stream, "sha256").hexdigest()


def commands(text):
    """Yield top-level SMT-LIB commands, ignoring comments and quoted contents."""
    start = None
    depth = 0
    quoted = None
    comment = False
    i = 0
    while i < len(text):
        c = text[i]
        if comment:
            comment = c != "\n"
        elif quoted:
            if c == quoted:
                if quoted == '"' and i + 1 < len(text) and text[i + 1] == '"':
                    i += 1
                else:
                    quoted = None
        elif c == ";":
            comment = True
        elif c in ('"', "|"):
            quoted = c
        elif c == "(":
            if depth == 0:
                start = i
            depth += 1
        elif c == ")":
            depth -= 1
            if depth < 0:
                raise ValueError("Unbalanced SMT-LIB parentheses")
            if depth == 0:
                yield start, i + 1, text[start:i + 1]
        i += 1
    if depth or quoted:
        raise ValueError("Unterminated SMT-LIB command or quoted token")


def qsat_input(text, tactic="qsat"):
    found = []
    for start, end, command in commands(text):
        if re.fullmatch(rf"\({SPACE}check-sat{SPACE}\)", command):
            found.append((start, end))
        elif re.match(rf"\({SPACE}(?:check-sat-assuming|check-sat-using|push|pop|reset)\b", command):
            raise ValueError("Expected a non-incremental check-sat benchmark")
    if len(found) != 1:
        raise ValueError(f"Expected exactly one check-sat, found {len(found)}")
    start, end = found[0]
    return text[:start] + f"(check-sat-using {tactic})" + text[end:]


def discover(root, per_family):
    families = defaultdict(list)
    for path in sorted(root.rglob("*.smt2")):
        relative = path.relative_to(root).as_posix()
        text = path.read_text(encoding="utf-8")
        status = None
        for _, _, command in commands(text):
            match = re.fullmatch(rf"\({SPACE}set-info{SPACE}:status{SPACE}(sat|unsat|unknown){SPACE}\)", command)
            if match:
                status = match[1]
        family = path.relative_to(root).parts[0]
        families[family].append({
            "path": relative, "family": family, "expected": status,
            "sha256": sha256(path),
        })
    selected = []
    for family in sorted(families):
        cases = families[family]
        if per_family:
            cases = sorted(cases, key=lambda c: hashlib.sha256(c["path"].encode()).hexdigest())
            cases = cases[:per_family]
        selected.extend(cases)
    return sorted(selected, key=lambda c: c["path"])


def classify(returncode, stdout, stderr, timed_out):
    if timed_out:
        return "timeout"
    if returncode != 0:
        return "crash" if returncode < 0 else "error"
    if "(error" in stdout or "(error" in stderr:
        return "error"
    answers = re.findall(r"^(sat|unsat|unknown)(?:,[^\n]*)?\s*$", stdout, re.MULTILINE)
    return answers[0] if len(answers) == 1 else "error"


def run_case(solver, path, output, timeout):
    command = [part.replace("{input}", str(path)) for part in solver["command"]]
    env = dict(os.environ, **solver.get("env", {}))
    start = time.perf_counter()
    timed_out = threading.Event()
    with output.with_suffix(".stdout").open("wb") as stdout, \
            output.with_suffix(".stderr").open("wb") as stderr:
        with subprocess.Popen(
            command, cwd=solver.get("cwd"), env=env, stdout=stdout, stderr=stderr,
            start_new_session=os.name == "posix",
        ) as process:
            def expire():
                if process.poll() is None:
                    timed_out.set()
                    try:
                        if os.name == "posix":
                            os.killpg(process.pid, signal.SIGKILL)
                        else:
                            process.kill()
                    except ProcessLookupError:
                        pass

            timer = threading.Timer(timeout, expire)
            timer.start()
            try:
                process.wait()
            except KeyboardInterrupt:
                expire()
                raise
            finally:
                timer.cancel()
                timer.join()
            returncode = process.returncode
    elapsed = time.perf_counter() - start
    stdout = output.with_suffix(".stdout").read_text(encoding="utf-8", errors="replace")
    stderr = output.with_suffix(".stderr").read_text(encoding="utf-8", errors="replace")
    return {
        "command": command, "returncode": returncode, "elapsed": elapsed,
        "result": classify(returncode, stdout, stderr, timed_out.is_set()),
        "statistics": dict(re.findall(r":([\w-]+)\s+([-+\d.eE]+)(?=\s|\))", stdout)),
    }


def solvers(args):
    result = []
    for name in ("baseline", "candidate"):
        binary = getattr(args, name)
        if not binary:
            continue
        binary = binary.resolve(strict=True)
        for mode in (("qsat", "default") if args.include_default else ("qsat",)):
            result.append({
                "name": f"{name}-{mode}", "qsat": mode == "qsat",
                "command": [str(binary), "-st", "{input}"],
                "executable_sha256": sha256(binary),
                "tactic": (
                    "(using-params qsat"
                    + (" :qsat_recursive_backjump true" if args.recursive_backjump else "")
                    + (" :qsat_use_qel false" if args.classic_mbp else "") + ")"
                ) if name == "candidate" and (args.recursive_backjump or args.classic_mbp) else "qsat",
            })
    if args.mucyc:
        root = args.mucyc.resolve(strict=True)
        binary = root / "main.exe"
        if not binary.is_file():
            binary = root / "_build" / "default" / "main.exe"
        binary = binary.resolve(strict=True)
        for name, config in (
            ("mucyc-progress", "mucyc_progress_ncr.json"),
            ("mucyc-no-progress", "mucyc.json"),
            ("paper-z3", "z3_smt.json"),
        ):
            config = root / "config" / "solver" / config
            result.append({
                "name": name, "qsat": False, "cwd": str(root),
                "command": [str(binary), "-c", str(config), "-p", "smt", "{input}"],
                "env": {"LD_LIBRARY_PATH": str(root / "lib")} if (root / "lib").is_dir() else {},
                "executable_sha256": sha256(binary), "config_sha256": sha256(config),
            })
    return result


def evaluate(args):
    root = args.corpus.resolve(strict=True)
    cases = discover(root, args.per_family)
    if not cases:
        raise ValueError(f"No SMT-LIB2 inputs under {root}")
    configurations = solvers(args)
    if not configurations:
        raise ValueError("Specify at least one of --baseline, --candidate, --mucyc")
    output = args.output.resolve()
    output.mkdir(parents=True, exist_ok=False)
    (output / "inputs").mkdir()
    (output / "raw").mkdir()
    manifest = {
        "corpus": str(root), "timeout": args.timeout, "per_family": args.per_family,
        "solvers": configurations, "cases": cases, "platform": platform.platform(),
        "created_utc": datetime.now(timezone.utc).isoformat(),
        "runner_sha256": sha256(Path(__file__)),
    }
    (output / "manifest.json").write_text(json.dumps(manifest, indent=2) + "\n")
    counts = {solver["name"]: Counter() for solver in configurations}
    records = []
    with (output / "results.jsonl").open("w", encoding="utf-8") as results:
        for index, case in enumerate(cases):
            path = root / case["path"]
            text = path.read_text(encoding="utf-8")
            if sha256(path) != case["sha256"]:
                raise ValueError(f"Input changed during evaluation: {path}")
            for solver in configurations:
                transformed = output / "inputs" / f"{index:05d}-{solver['name']}.smt2"
                if solver["qsat"]:
                    transformed.write_text(qsat_input(text, solver.get("tactic", "qsat")), encoding="utf-8")
                prefix = output / "raw" / f"{index:05d}-{solver['name']}"
                record = dict(case, solver=solver["name"])
                record.update(run_case(solver, transformed if solver["qsat"] else path, prefix, args.timeout))
                if case["expected"] in ("sat", "unsat") and record["result"] in ("sat", "unsat") \
                        and case["expected"] != record["result"]:
                    record["answer"] = record["result"]
                    record["result"] = "wrong"
                counts[solver["name"]][record["result"]] += 1
                results.write(json.dumps(record) + "\n")
                results.flush()
                records.append(record)
            print(f"{index + 1}/{len(cases)} {case['path']}", flush=True)
    by_case = defaultdict(dict)
    for record in records:
        by_case[record["path"]][record["solver"]] = record
    disagreements = []
    for path, answers_by_solver in by_case.items():
        answers = {r["result"] for r in answers_by_solver.values() if r["result"] in ("sat", "unsat")}
        if len(answers) > 1:
            disagreements.append(path)
    comparisons = {}
    if "baseline-qsat" in counts:
        for solver in counts:
            if solver == "baseline-qsat":
                continue
            rescued, lost = [], []
            for path, answers in by_case.items():
                baseline = answers["baseline-qsat"]["result"] in ("sat", "unsat")
                solved = answers[solver]["result"] in ("sat", "unsat")
                if solved and not baseline:
                    rescued.append(path)
                elif baseline and not solved:
                    lost.append(path)
            comparisons[solver] = {"rescued": rescued, "lost": lost}
    summary = {"counts": counts, "disagreements": disagreements, "vs_baseline": comparisons}
    (output / "summary.json").write_text(json.dumps(summary, indent=2) + "\n")
    print(json.dumps(summary, indent=2), flush=True)
    return int(bool(disagreements) or any(c["wrong"] or c["error"] or c["crash"] for c in counts.values()))


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--corpus", type=Path, required=True, help="The extracted non-incremental/LRA directory")
    parser.add_argument("--baseline", type=Path)
    parser.add_argument("--candidate", type=Path)
    parser.add_argument("--mucyc", type=Path, help="Artifact root with main.exe and config/ (optional lib/)")
    parser.add_argument("--include-default", action="store_true")
    parser.add_argument("--recursive-backjump", action="store_true", help="Enable recursive projection in candidate QSAT only")
    parser.add_argument("--classic-mbp", action="store_true", help="Disable egraph-based projection in candidate QSAT only")
    parser.add_argument("--timeout", type=float, default=300)
    parser.add_argument("--per-family", type=int, default=0, help="Deterministic pilot sample; 0 evaluates the full corpus")
    parser.add_argument("--output", type=Path, required=True, help="New output directory for manifests, raw logs and results")
    args = parser.parse_args()
    if not math.isfinite(args.timeout) or args.timeout <= 0 or args.per_family < 0:
        parser.error("--timeout must be positive and --per-family must be non-negative")
    return evaluate(args)


if __name__ == "__main__":
    raise SystemExit(main())
