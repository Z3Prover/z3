"""Measure independent-checker coverage on incremental SMT-LIB sessions."""

import argparse
from collections import Counter
import json
from pathlib import Path
import re
import subprocess
import time

from run_checker_regressions import (
    STATISTICS, discover, file_sha256, memory_limit, positive_float, solver_timeout,
)


NNF = re.compile(
    r"^; proof-nnf nnf-pos-roots=(\d+) nnf-pos-pending=(\d+) "
    r"nnf-neg-roots=(\d+) nnf-neg-pending=(\d+)$")
PROOF = re.compile(r"^; proof-check (ACCEPT|PARTIAL [1-9]\d*|REJECT|UNKNOWN .+)$")


def summarize_log(path):
    counts = Counter()
    awaiting_nnf = False
    with path.open(encoding="utf-8", errors="replace") as stream:
        for line in stream:
            line = line.rstrip("\r\n")
            if line in ("sat", "unsat", "unknown"):
                counts["solver_" + line] += 1
            match = PROOF.fullmatch(line)
            if match:
                verdict = match[1].split()[0].lower()
                counts["proof_" + verdict] += 1
                awaiting_nnf = True
            match = NNF.fullmatch(line)
            if match:
                if not awaiting_nnf:
                    raise ValueError("NNF statistics without a preceding proof verdict")
                pos, pos_pending, neg, neg_pending = map(int, match.groups())
                if pos_pending > pos or neg_pending > neg:
                    raise ValueError("NNF pending count exceeds observed root count")
                counts.update({"nnf_pos_roots": pos, "nnf_pos_pending": pos_pending,
                               "nnf_neg_roots": neg, "nnf_neg_pending": neg_pending,
                               "nnf_reported_proofs": 1})
                awaiting_nnf = False
            if line.startswith("; proof-stats "):
                match = STATISTICS.fullmatch(line.removeprefix("; proof-stats "))
                if match:
                    counts["phase_reported_proofs"] += 1
                    for name, value in zip(("solve", "marshal", "check"), match.groups()[:3]):
                        counts["phase_" + name + "_ms"] += float(value)
    counts["proof_verdicts"] = sum(counts["proof_" + name]
                                   for name in ("accept", "partial", "reject", "unknown"))
    counts["unsat_without_verdict"] = max(0, counts["solver_unsat"] - counts["proof_verdicts"])
    return dict(counts)


def run(args):
    corpus = args.corpus.resolve()
    paths, discovered = discover(corpus, ".", 0)
    if args.max_cases:
        paths = paths[:args.max_cases]
    output = args.output.resolve()
    output.mkdir(parents=True, exist_ok=False)
    logs = output / "logs"
    logs.mkdir()
    selection = {
        "corpus": str(corpus), "corpus_commit": args.corpus_commit,
        "checker": str(args.checker.resolve()), "discovered": discovered,
        "checker_sha256": file_sha256(args.checker.resolve()),
        "checker_arguments": getattr(args, "checker_arg", []),
        "selected": len(paths), "solver_timeout_ms": args.solver_timeout_ms,
        "case_timeout_seconds": args.case_timeout_seconds,
        "total_timeout_seconds": args.total_timeout_seconds,
        "memory_limit_mb": args.memory_limit_mb,
        "inputs": [{"path": p.relative_to(corpus).as_posix(), "sha256": file_sha256(p)}
                   for p in paths],
    }
    (output / "selection.json").write_text(json.dumps(selection, indent=2) + "\n", encoding="utf-8")
    deadline = time.monotonic() + args.total_timeout_seconds
    totals = Counter()
    with (output / "results.jsonl").open("w", encoding="utf-8") as results:
        for index, (path, metadata) in enumerate(zip(paths, selection["inputs"])):
            remaining = deadline - time.monotonic()
            row = dict(metadata)
            if remaining <= 0:
                row["outcome"] = "NOT_RUN"
            else:
                stdout_path = logs / f"{index:06d}.stdout"
                stderr_path = logs / f"{index:06d}.stderr"
                start = time.monotonic()
                with path.open("rb") as source, stdout_path.open("wb") as stdout, stderr_path.open("wb") as stderr:
                    try:
                        result = subprocess.run(
                            [str(args.checker.resolve()), *getattr(args, "checker_arg", []),
                             "--interactive", "--diagnostics",
                             "--timeout-ms", str(args.solver_timeout_ms)],
                            stdin=source, stdout=stdout, stderr=stderr,
                            timeout=min(args.case_timeout_seconds, remaining),
                            preexec_fn=(lambda: memory_limit(args.memory_limit_mb))
                            if args.memory_limit_mb else None)
                        row["returncode"] = result.returncode
                        row["outcome"] = ("COMPLETED" if result.returncode in (0, 1, 3, 5)
                                          else "ERROR" if result.returncode == 2 else "CRASH")
                    except subprocess.TimeoutExpired:
                        row.update(outcome="TIMEOUT", returncode=None)
                row.update(wall_seconds=time.monotonic() - start,
                           stdout=stdout_path.relative_to(output).as_posix(),
                           stderr=stderr_path.relative_to(output).as_posix())
                try:
                    row["counts"] = summarize_log(stdout_path)
                    if (row["outcome"] == "COMPLETED" and
                            row["counts"].get("solver_unsat", 0) != row["counts"]["proof_verdicts"]):
                        row["outcome"] = "PROTOCOL_ERROR"
                    totals.update(row["counts"])
                except ValueError as exc:
                    row.update(outcome="PROTOCOL_ERROR", error=str(exc))
            totals["sessions_" + row["outcome"].lower()] += 1
            results.write(json.dumps(row) + "\n")
            results.flush()
            print(f'{index + 1}/{len(paths)} {row["outcome"]}: {row["path"]}', flush=True)
    (output / "summary.json").write_text(json.dumps(dict(totals), indent=2, sort_keys=True) + "\n",
                                          encoding="utf-8")
    return int(any(totals["sessions_" + x] for x in ("error", "crash", "protocol_error")))


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--checker", type=Path, required=True)
    parser.add_argument("--checker-arg", action="append", default=[],
                        help="Additional checker argument; repeat as --checker-arg=--definition-replay")
    parser.add_argument("--corpus", type=Path, required=True)
    parser.add_argument("--corpus-commit", required=True)
    parser.add_argument("--output", type=Path, required=True)
    parser.add_argument("--max-cases", type=int, default=0)
    parser.add_argument("--solver-timeout-ms", type=solver_timeout, default=10000)
    parser.add_argument("--case-timeout-seconds", type=positive_float, default=60)
    parser.add_argument("--total-timeout-seconds", type=positive_float, default=3600)
    parser.add_argument("--memory-limit-mb", type=int, default=4096)
    args = parser.parse_args()
    if args.max_cases < 0 or args.memory_limit_mb < 0:
        parser.error("case and memory limits must be nonnegative")
    return run(args)


if __name__ == "__main__":
    raise SystemExit(main())
