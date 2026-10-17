"""Benchmark the native SMT-LIB checker; report coverage, not solver-only passes."""

import argparse
from collections import Counter
import csv
import json
import math
import os
from pathlib import Path
import re
import statistics
import subprocess
import sys
import time


VERDICTS = {
    0: ("ACCEPT", r"ACCEPT"),
    1: ("REJECT", r"REJECT"),
    3: ("PARTIAL", r"PARTIAL [1-9][0-9]*"),
    4: ("SAT", r"SAT"),
    5: ("UNKNOWN", r"UNKNOWN .+"),
}
OUTCOMES = (
    "ACCEPT", "PARTIAL", "REJECT", "SAT", "UNKNOWN", "TIMEOUT",
    "ERROR", "CRASH", "PROTOCOL_ERROR", "NOT_RUN",
)
ERRORS = {"ERROR", "CRASH", "PROTOCOL_ERROR"}
STATISTICS = re.compile(
    r"^solve_ms=([\d.]+) marshal_ms=([\d.]+) check_ms=([\d.]+) "
    r"expressions=(\d+) declarations=(\d+) proof_nodes=(\d+)$", re.MULTILINE)


def classify(returncode, stdout):
    if returncode == 2:
        return "ERROR"
    if returncode not in VERDICTS:
        return "CRASH"
    outcome, pattern = VERDICTS[returncode]
    return outcome if re.fullmatch(pattern, stdout.strip()) else "PROTOCOL_ERROR"


def discover(corpus, relative_path, max_cases):
    root = (corpus / relative_path).resolve()
    if not root.is_relative_to(corpus) or not root.is_dir():
        raise ValueError("Corpus path must be an existing directory inside the corpus checkout")
    paths = sorted(root.rglob("*.smt2"))
    if not paths:
        raise ValueError(f"No .smt2 files found in {root}")
    if any(not path.resolve().is_relative_to(corpus) for path in paths):
        raise ValueError("Corpus contains an SMT-LIB symlink outside the checkout")
    return paths[:max_cases] if max_cases else paths, len(paths)


def memory_limit(megabytes):
    import resource
    resource.setrlimit(resource.RLIMIT_AS, (megabytes * 1024**2,) * 2)


def read_log(path):
    with path.open("r", encoding="utf-8", errors="replace") as stream:
        return stream.read(65536)


def run_case(command, path, output, index, timeout, megabytes):
    stem = f"logs/{index:06d}"
    row = {"path": path, "stdout": stem + ".stdout", "stderr": stem + ".stderr"}
    start = time.perf_counter()
    with (output / row["stdout"]).open("wb") as stdout, (output / row["stderr"]).open("wb") as stderr:
        try:
            result = subprocess.run(
                command, stdout=stdout, stderr=stderr, timeout=timeout,
                preexec_fn=(lambda: memory_limit(megabytes)) if megabytes else None)
            row["returncode"] = result.returncode
        except subprocess.TimeoutExpired:
            row["returncode"] = None
            row["outcome"] = "TIMEOUT"
    row["wall_seconds"] = time.perf_counter() - start
    text = read_log(output / row["stdout"]).strip()
    row["verdict"] = text[:4096]
    if "outcome" not in row:
        row["outcome"] = classify(row["returncode"], text)
    match = STATISTICS.search(read_log(output / row["stderr"]))
    if match:
        row["statistics"] = dict(zip(
            ("solve_ms", "marshal_ms", "check_ms", "expressions", "declarations", "proof_nodes"),
            [float(value) for value in match.groups()[:3]] +
            [int(value) for value in match.groups()[3:]]))
    return row


def run_suite(args):
    corpus = args.corpus.resolve()
    paths, discovered = discover(corpus, args.corpus_path, args.max_cases)
    checker = args.checker.expanduser().resolve()
    if args.memory_limit_mb and sys.platform != "linux":
        raise ValueError("The address-space limit requires Linux; use --memory-limit-mb 0 elsewhere")
    version = subprocess.run([str(checker), "--version"], check=True, capture_output=True,
                             text=True, timeout=10).stdout.strip()
    output = args.output
    (output / "logs").mkdir(parents=True, exist_ok=True)
    selection = {
        "corpus_path": args.corpus_path, "corpus_commit": args.corpus_commit,
        "z3_commit": os.environ.get("GITHUB_SHA", ""),
        "checker_version": version, "discovered": discovered,
        "paths": [path.relative_to(corpus).as_posix() for path in paths],
        "solver_timeout_ms": args.solver_timeout_ms,
        "case_timeout_seconds": args.case_timeout_seconds,
        "total_timeout_seconds": args.total_timeout_seconds,
        "memory_limit_mb": args.memory_limit_mb,
    }
    (output / "selection.json").write_text(json.dumps(selection, indent=2) + "\n", encoding="utf-8")
    deadline = time.perf_counter() + args.total_timeout_seconds
    outcomes = Counter()
    with (output / "results.jsonl").open("w", encoding="utf-8") as stream:
        for index, (path, relative) in enumerate(zip(paths, selection["paths"])):
            remaining = deadline - time.perf_counter()
            if remaining <= 0:
                row = {"path": relative, "outcome": "NOT_RUN", "reason": "Total time budget exhausted"}
            else:
                row = run_case(
                    [str(checker), "--stats", "--timeout-ms", str(args.solver_timeout_ms), str(path)],
                    relative, output, index, min(args.case_timeout_seconds, remaining),
                    args.memory_limit_mb)
            stream.write(json.dumps(row) + "\n")
            stream.flush()
            outcomes[row["outcome"]] += 1
            print(f'{index + 1}/{len(paths)} {row["outcome"]}: {relative}', flush=True)
    return int(any(outcomes[outcome] for outcome in ERRORS) or
               outcomes["NOT_RUN"] == len(paths))


def percentage(count, total):
    return f"{100 * count / total:.1f}%" if total else "n/a"


def cell(value):
    return str(value).replace("|", "\\|").replace("`", "'").replace("\n", " ").replace("\r", " ")


def report(output):
    output.mkdir(parents=True, exist_ok=True)
    selection_path, results_path = output / "selection.json", output / "results.jsonl"
    selection = json.loads(selection_path.read_text(encoding="utf-8")) if selection_path.exists() else {}
    results, warnings = [], []
    if results_path.exists():
        lines = results_path.read_text(encoding="utf-8").splitlines(keepends=True)
        for index, line in enumerate(lines):
            try:
                results.append(json.loads(line))
            except json.JSONDecodeError:
                if index != len(lines) - 1 or line.endswith("\n"):
                    raise
                warnings.append("Incomplete final result record after interruption; raw results.jsonl retained.")
    recorded = {row["path"] for row in results}
    results.extend({"path": path, "outcome": "NOT_RUN", "reason": "Runner stopped before this case"}
                   for path in selection.get("paths", []) if path not in recorded)
    counts = Counter(row["outcome"] for row in results)
    tested = len(results) - counts["NOT_RUN"]
    times = [row["wall_seconds"] for row in results if "wall_seconds" in row]
    build_path = output / "build.json"
    build = json.loads(build_path.read_text(encoding="utf-8")) if build_path.exists() else {}
    phases = {
        name: sum(row.get("statistics", {}).get(name, 0) for row in results)
        for name in ("solve_ms", "marshal_ms", "check_ms")
    }
    summary = {
        "selection": selection, "build": build,
        "build_outcome": os.environ.get("BUILD_OUTCOME", "not recorded"),
        "corpus_outcome": os.environ.get("CORPUS_OUTCOME", "not recorded"),
        "runner_outcome": os.environ.get("RUNNER_OUTCOME", "not recorded"),
        "toolchain_outcome": os.environ.get("TOOLCHAIN_OUTCOME", "not recorded"),
        "harness_outcome": os.environ.get("HARNESS_OUTCOME", "not recorded"),
        "selected": len(results), "tested": tested,
        "counts": {outcome: counts[outcome] for outcome in OUTCOMES},
        "success_rate": counts["ACCEPT"] / tested if tested else None,
        "uncertified_rate": (tested - counts["ACCEPT"]) / tested if tested else None,
        "wall_seconds": sum(times),
        "median_seconds": statistics.median(times) if times else None,
        "p95_seconds": sorted(times)[math.ceil(0.95 * len(times)) - 1] if times else None,
        "phase_totals_ms": phases,
        "phase_statistics_cases": sum("statistics" in row for row in results),
        "warnings": warnings,
    }
    (output / "summary.json").write_text(json.dumps(summary, indent=2) + "\n", encoding="utf-8")
    with (output / "results.csv").open("w", newline="", encoding="utf-8") as stream:
        fields = ("path", "outcome", "wall_seconds", "returncode", "verdict", "reason")
        writer = csv.DictWriter(stream, fieldnames=fields, extrasaction="ignore")
        writer.writeheader()
        writer.writerows(results)
    lines = [
        "# Pulse verification and native F* checker regressions", "",
        "**Scope:** the build verifies the in-memory Pulse checkers and their regressions. "
        "The SMT-LIB corpus executes the native extracted F* checker; Pulse is not linked into that executable.",
        "Build self-tests cover Pulse equality/rewriter, justification, and Farkas checkers; "
        "resolution and polynomial-certificate regressions; and native bridge/CLI tests.",
        "Only `ACCEPT` certifies an obligation-free closed refutation. `PARTIAL`, `REJECT`, "
        "`SAT`, and `UNKNOWN` are never counted as proof-checking successes.", "",
        f'- Build and self-tests: **{cell(summary["build_outcome"])}**; '
        f'corpus checkout: **{cell(summary["corpus_outcome"])}**; '
        f'regression runner: **{cell(summary["runner_outcome"])}**.',
        f'- Toolchain setup: **{cell(summary["toolchain_outcome"])}**; '
        f'harness tests: **{cell(summary["harness_outcome"])}**; '
        f'F*: `{cell(build.get("fstar_version", "not recorded"))}`; '
        f'OCaml: `{cell(build.get("ocaml_version", "not recorded"))}`.',
        f'- Build wall time: {build.get("wall_seconds", "not recorded")} seconds.',
        f'- Z3 commit: `{cell(selection.get("z3_commit", os.environ.get("GITHUB_SHA", "")))}`; '
        f'checker producer version: `{cell(selection.get("checker_version", "not recorded"))}`.',
        f'- z3test commit: `{cell(selection.get("corpus_commit", "not recorded"))}`; '
        f'path: `{cell(selection.get("corpus_path", "not recorded"))}`.',
        f'- Discovered: {selection.get("discovered", 0)}; selected: {len(results)}; '
        f'attempted: {tested}; not run: {counts["NOT_RUN"]}.',
        f'- Proof-checking success rate: **{percentage(counts["ACCEPT"], tested)}**; '
        f'uncertified/failure rate: **{percentage(tested - counts["ACCEPT"], tested)}** '
        "(denominator: all attempted files, including SAT and unknown).",
        f'- Solver timeout: {selection.get("solver_timeout_ms", "n/a")} ms; '
        f'whole-case timeout: {selection.get("case_timeout_seconds", "n/a")} s; '
        f'total test budget: {selection.get("total_timeout_seconds", "n/a")} s; '
        f'address-space limit: {selection.get("memory_limit_mb", "n/a")} MiB (0 = unlimited).', "",
        "| Outcome | Files | Rate among attempted |",
        "|---|---:|---:|",
    ]
    for outcome in OUTCOMES:
        lines.append(f'| {outcome} | {counts[outcome]} | '
                     f'{percentage(counts[outcome], tested) if outcome != "NOT_RUN" else "not attempted"} |')
    if not selection:
        lines += ["", "**No corpus selection was recorded; no test success is claimed.**"]
    for warning in warnings:
        lines += ["", f"**Warning:** {warning}"]
    if times:
        lines += ["", "## Timing", "",
                  f'Total case wall time: {sum(times):.3f} s; median: {summary["median_seconds"]:.3f} s; '
                  f'p95 (nearest rank): {summary["p95_seconds"]:.3f} s.',
                  f'Stats available for {summary["phase_statistics_cases"]}/{tested} attempted files. '
                  f'Phase totals for those files only: solve {phases["solve_ms"]:.3f} ms, '
                  f'marshal {phases["marshal_ms"]:.3f} ms, check {phases["check_ms"]:.3f} ms. '
                  "SAT, unknown, and interrupted runs may have no phase statistics."]
    lines += ["", "## Per-file results (first 100; full list in results.csv)", "",
              "| File | Outcome | Wall seconds |", "|---|---|---:|"]
    for row in results[:100]:
        elapsed = f'{row["wall_seconds"]:.3f}' if "wall_seconds" in row else "-"
        lines.append(f'| {cell(row["path"])} | {row["outcome"]} | {elapsed} |')
    lines += ["", "Inputs are recursively selected `.smt2` files, in sorted order, without modification. "
              "Manifest `.txt` lists and pre-generated `.proof` files are not executed. The native API "
              "checks the parsed final assertion set, not an incremental command transcript. "
              "These are coverage measurements of current proof production/checking, not validation "
              "of z3test's other proof backends or unconditional SMT-LIB soundness.",
              "Logs, incremental results.jsonl, results.csv, selection.json, and summary.json "
              "are retained as artifacts. Timeouts and unsupported/partial proofs are measurements; "
              "build/self-test failures, errors, crashes, and protocol mismatches fail the workflow.", ""]
    (output / "report.md").write_text("\n".join(lines), encoding="utf-8")


def positive_float(value):
    number = float(value)
    if not math.isfinite(number) or number <= 0:
        raise argparse.ArgumentTypeError("must be a finite positive number")
    return number


def nonnegative_int(value):
    number = int(value)
    if number < 0:
        raise argparse.ArgumentTypeError("must be nonnegative")
    return number


def solver_timeout(value):
    number = int(value)
    if not 0 < number <= 4294967295:
        raise argparse.ArgumentTypeError("must be between 1 and 4294967295")
    return number


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    commands = parser.add_subparsers(dest="command", required=True)
    run = commands.add_parser("run")
    run.add_argument("--checker", type=Path, required=True)
    run.add_argument("--corpus", type=Path, required=True)
    run.add_argument("--corpus-path", default="regressions/proofs")
    run.add_argument("--corpus-commit", required=True)
    run.add_argument("--max-cases", type=nonnegative_int, default=0)
    run.add_argument("--solver-timeout-ms", type=solver_timeout, default=10000)
    run.add_argument("--case-timeout-seconds", type=positive_float, default=60)
    run.add_argument("--total-timeout-seconds", type=positive_float, default=1800)
    run.add_argument("--memory-limit-mb", type=nonnegative_int, default=0)
    run.add_argument("--output", type=Path, required=True)
    summarize = commands.add_parser("report")
    summarize.add_argument("--output", type=Path, required=True)
    args = parser.parse_args()
    if args.command == "report":
        report(args.output)
        return 0
    return run_suite(args)


if __name__ == "__main__":
    sys.exit(main())
