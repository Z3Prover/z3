#!/usr/bin/env python3
"""
Compare z3 string solver configurations, and optionally against external solvers.

We always run three z3 configurations:
    nseq_md  monadic decomposition (parikh off, eager regex factorization)
    nseq_pa  parikh (parikh on, no regex factorization)
    seq      the old/baseline string solver

Optionally compare against external solvers:
    zipt     ZIPT solver (--zipt /path/to/zipt)
    ostrich  Ostrich solver (--ostrich /path/to/ostrich)
    noodler  z3-noodler solver (--noodler /path/to/z3noodler)

Usage:
    python compare_seq_solvers.py <path-to-smtlib-files> --z3 /path/to/z3
        [--zipt /path/to/zipt] [--ostrich /path/to/ostrich] [--noodler /path/to/noodler]
        [--ext .smt2]

Finds all .smt2 files under the given path, runs the solvers with a configurable timeout,
and reports timeouts, divergences, and summary statistics.
"""

import argparse
import random
import re
import subprocess
import sys
import time
from collections import defaultdict
from concurrent.futures import ThreadPoolExecutor, as_completed
from pathlib import Path

DEFAULT_TIMEOUT = 5  # seconds
COMMON_ARGS = ["model_validate=true"]

# All three configurations are always run.
SOLVERS = {
    "nseq_md": ["smt.string_solver=nseq", "smt.nseq.parikh=false", "smt.nseq.eager=false",
                "smt.nseq.regex_factorization_threshold=10000000", "smt.nseq.regex_factorization_eager=true"],
    "nseq_pa": ["smt.string_solver=nseq", "smt.nseq.parikh=false", "smt.nseq.eager=false",
                "smt.nseq.regex_factorization_threshold=0", "smt.nseq.regex_factorization_eager=false"],
    "seq":     ["smt.string_solver=seq"],
}

# Ordered list of the z3 configuration names (excludes the external zipt solver).
SOLVER_NAMES = list(SOLVERS.keys())


_STATUS_RE = re.compile(r'\(\s*set-info\s+:status\s+(sat|unsat|unknown)\s*\)')


def read_smtlib_status(smt_file: Path) -> str:
    """Read the expected status from the SMT-LIB (set-info :status ...) directive.
    Returns 'sat', 'unsat', or 'unknown'.
    """
    try:
        text = smt_file.read_text(encoding="utf-8", errors="replace")
        m = _STATUS_RE.search(text)
        if m:
            return m.group(1)
    except OSError:
        pass
    return "unknown"


def determine_status(solver_results: dict[str, str], smtlib_status: str) -> str:
    """Determine the ground-truth status of a problem.
    If the solvers that gave a definite (sat/unsat) answer all agree, use that;
    if they disagree, fall back to the SMT-LIB annotation; otherwise 'unknown'.
    """
    definite = {"sat", "unsat"}
    found = {r for r in solver_results.values() if r in definite}
    if len(found) == 1:
        return found.pop()
    # No definite answer, or a disagreement among definite answers.
    if smtlib_status in definite:
        return smtlib_status
    return "unknown"


def _parse_result(output: str) -> str:
    """Extract the first sat/unsat/unknown line from solver output."""
    has_invalid_model = "an invalid model was generated" in output
    for line in output.splitlines():
        tok = line.strip().lower()
        if tok in ("sat", "unsat"):
            if tok == "sat" and has_invalid_model:
                return "invalid"
            return tok
        if tok == "unknown":
            return "timeout"
    return "timeout"


def run_z3(z3_bin: str, smt_file: Path, solver_args: list[str], timeout_s: int = DEFAULT_TIMEOUT) -> tuple[str, float]:
    """Run z3 on a file with the given solver arguments.
    Returns (result, elapsed) where result is 'sat', 'unsat', or 'timeout'/'error'.
    """
    timeout_ms = timeout_s * 1000
    cmd = [z3_bin, f"-t:{timeout_ms}"] + solver_args + COMMON_ARGS + [str(smt_file)]
    start = time.monotonic()
    try:
        proc = subprocess.run(cmd, capture_output=True, shell=True, text=True,
                              timeout=timeout_s + 5)
        elapsed = time.monotonic() - start
        return _parse_result(proc.stdout.strip()), elapsed
    except subprocess.TimeoutExpired:
        elapsed = time.monotonic() - start
        return "timeout", elapsed
    except Exception as e:
        elapsed = time.monotonic() - start
        return f"error:{e}", elapsed


def run_external_solver(binary: str, smt_file: Path, timeout_s: int = DEFAULT_TIMEOUT,
                        extra_args: list[str] | None = None) -> tuple[str, float]:
    """Run an external solver on a file. Returns (result, elapsed).

    Passes -t:{timeout_ms} as the first argument, matching the Z3/ZIPT convention.
    Supply extra_args for any solver-specific flags that precede the file path.
    """
    timeout_ms = timeout_s * 1000
    cmd = [binary, f"-t:{timeout_ms}"] + (extra_args or []) + [str(smt_file)]
    start = time.monotonic()
    try:
        proc = subprocess.run(cmd, capture_output=True, text=True,
                              timeout=timeout_s + 5)
        elapsed = time.monotonic() - start
        return _parse_result(proc.stdout.strip()), elapsed
    except subprocess.TimeoutExpired:
        elapsed = time.monotonic() - start
        return "timeout", elapsed
    except Exception as e:
        elapsed = time.monotonic() - start
        return f"error:{e}", elapsed


def classify(solver_results: dict[str, str]) -> str:
    """Classify the results of all z3 configurations into a category."""
    definite = {"sat", "unsat"}
    results = list(solver_results.values())

    if any(r == "invalid" for r in results):
        return "invalid_model"

    n_timeout = sum(1 for r in results if r == "timeout")
    if n_timeout == len(results):
        return "all_timeout"

    # Among the configurations that terminated:
    terminated = [r for r in results if r != "timeout"]
    found = {r for r in terminated if r in definite}
    if len(found) > 1:
        return "diverge"
    if any(r == "unknown" for r in terminated):
        return "unknown_involved"
    # All terminating configurations agree on a definite answer.
    if n_timeout == 0:
        return "all_agree"
    return "agree_some_timeout"


def process_file(z3_bin: str, smt_file: Path, timeout_s: int = DEFAULT_TIMEOUT,
                 external_bins: dict[str, str] | None = None) -> dict:
    """Run all z3 configurations and any external solvers on smt_file.

    external_bins maps solver label (e.g. 'zipt', 'ostrich', 'noodler') to binary path.
    """
    solver_results: dict[str, str] = {}
    solver_times: dict[str, float] = {}
    for name in SOLVER_NAMES:
        res, t = run_z3(z3_bin, smt_file, SOLVERS[name], timeout_s)
        solver_results[name] = res
        solver_times[name] = t

    cat = classify(solver_results)
    smtlib_status = read_smtlib_status(smt_file)
    status = determine_status(solver_results, smtlib_status)
    result: dict = {
        "file":          smt_file,
        "category":      cat,
        "smtlib_status": smtlib_status,
        "status":        status,
    }
    for name in SOLVER_NAMES:
        result[name] = solver_results[name]
        result[f"t_{name}"] = solver_times[name]

    for label, binary in (external_bins or {}).items():
        res, t = run_external_solver(binary, smt_file, timeout_s)
        result[label] = res
        result[f"t_{label}"] = t

    return result


def main():
    parser = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    parser.add_argument("path", help="Directory containing SMT-LIB2 files")
    parser.add_argument("--z3", required=True, metavar="PATH", help="Path to z3 binary")
    parser.add_argument("--ext", default=".smt2", help="File extension to search for (default: .smt2)")
    parser.add_argument("--jobs", type=int, default=4, metavar="N",
                        help="Number of parallel worker threads (default: 4)")
    parser.add_argument("--max-per-folder", type=int, default=None, metavar="N",
                        help="Max SMT2 files to benchmark per subfolder; "
                             "excess files are randomly sampled down to this limit")
    parser.add_argument("--timeout", type=int, default=DEFAULT_TIMEOUT, metavar="SEC",
                        help=f"Per-solver timeout in seconds (default: {DEFAULT_TIMEOUT})")
    parser.add_argument("--zipt", metavar="PATH", default=None,
                        help="Path to ZIPT binary (optional)")
    parser.add_argument("--ostrich", metavar="PATH", default=None,
                        help="Path to Ostrich binary (optional)")
    parser.add_argument("--noodler", metavar="PATH", default=None,
                        help="Path to z3-noodler binary (optional)")
    parser.add_argument("--csv", metavar="FILE", help="Also write results to a CSV file")
    args = parser.parse_args()

    z3_bin = args.z3
    timeout_s = args.timeout

    # Collect external solvers in declaration order so output columns are stable.
    external_bins: dict[str, str] = {}
    if args.zipt:    external_bins["zipt"]    = args.zipt
    if args.ostrich: external_bins["ostrich"] = args.ostrich
    if args.noodler: external_bins["noodler"] = args.noodler
    ext_names = list(external_bins.keys())

    root = Path(args.path)
    if not root.exists():
        print(f"Error: path does not exist: {root}", file=sys.stderr)
        sys.exit(1)

    files = sorted(root.rglob(f"*{args.ext}"))
    if not files:
        print(f"No {args.ext} files found under {root}", file=sys.stderr)
        sys.exit(1)

    if args.max_per_folder is not None:
        by_folder: dict[Path, list[Path]] = defaultdict(list)
        for f in files:
            by_folder[f.parent].append(f)
        sampled: list[Path] = []
        for folder_files in by_folder.values():
            if len(folder_files) > args.max_per_folder:
                sampled.extend(random.sample(folder_files, args.max_per_folder))
            else:
                sampled.extend(folder_files)
        files = sorted(sampled)
        print(f"Sampling: {len(files)} files selected "
              f"(max {args.max_per_folder} per subfolder, {len(by_folder)} subfolder(s))")

    all_solver_labels = SOLVER_NAMES + ext_names
    print(f"Found {len(files)} files. Solvers: {', '.join(all_solver_labels)}. "
          f"Workers: {args.jobs}, timeout: {timeout_s}s\n")

    results = []
    pool = ThreadPoolExecutor(max_workers=args.jobs)
    futures = {pool.submit(process_file, z3_bin, f, timeout_s, external_bins): f for f in files}
    done = 0
    try:
        for fut in as_completed(futures):
            done += 1
            r = fut.result()
            results.append(r)
            solver_part = "  ".join(f"{name}={r[name]:8s} ({r[f't_{name}']:.1f}s)" for name in SOLVER_NAMES)
            ext_part = "".join(f"  {label}={r[label]:8s} ({r[f't_{label}']:.1f}s)" for label in ext_names)
            print(f"[{done:4d}/{len(files)}] {r['category']:20s}  {solver_part}{ext_part}  {r['file'].parent.name}/{r['file'].name}")
    except KeyboardInterrupt:
        print("\nInterrupted — cancelling pending tasks.", file=sys.stderr)
        pool.shutdown(wait=False, cancel_futures=True)
        sys.exit(130)
    else:
        pool.shutdown(wait=True)

    # ── Summary ──────────────────────────────────────────────────────────────
    categories = {
        "invalid_model":      [],
        "all_timeout":        [],
        "agree_some_timeout": [],
        "all_agree":          [],
        "unknown_involved":   [],
        "diverge":            [],
    }
    for r in results:
        categories.setdefault(r["category"], []).append(r)

    print("\n" + "="*70)
    print("TOTALS")
    for cat, items in categories.items():
        print(f"  {cat:40s}: {len(items)}")
    print(f"{'='*70}")

    # ── Per-solver timeout & divergence file lists ─────────────────────────
    diverged = categories["diverge"]

    def _print_file_list(label: str, items: list[dict]):
        print(f"\n{'─'*70}")
        print(f"  {label} ({len(items)} files)")
        print(f"{'─'*70}")
        for r in sorted(items, key=lambda x: x["file"]):
            print(f"  {r['file']}")

    for name in SOLVER_NAMES:
        timeouts = [r for r in results if r[name] == "timeout"]
        if timeouts:
            _print_file_list(f"{name.upper()} TIMES OUT", timeouts)

    for label in ext_names:
        timeouts = [r for r in results if r[label] == "timeout"]
        if timeouts:
            _print_file_list(f"{label.upper()} TIMES OUT", timeouts)

    all_to = categories["all_timeout"]
    if all_to:
        _print_file_list("ALL Z3 CONFIGURATIONS TIME OUT", all_to)
    invalid_models = categories.get("invalid_model", [])
    if invalid_models:
        _print_file_list("INVALID MODEL GENERATED", invalid_models)

    if ext_names:
        all_ext_to = [r for r in results
                      if all(r[name] == "timeout" for name in SOLVER_NAMES)
                      and all(r[label] == "timeout" for label in ext_names)]
        if all_ext_to:
            _print_file_list("ALL SOLVERS TIME OUT", all_ext_to)

    if diverged:
        _print_file_list("DIVERGE among z3 configurations (sat vs unsat)", diverged)

    definite = {"sat", "unsat"}
    for label in ext_names:
        ext_diverged = [r for r in results
                        if r[label] in definite
                        and any(r[name] in definite and r[name] != r[label] for name in SOLVER_NAMES)]
        if ext_diverged:
            _print_file_list(f"DIVERGE involving {label.upper()}", ext_diverged)

    print()

    # ── Problem status statistics ────────────────────────────────────────────
    status_counts = {"sat": 0, "unsat": 0, "unknown": 0}
    for r in results:
        status_counts[r["status"]] = status_counts.get(r["status"], 0) + 1

    total = len(results)
    pct = lambda n: (100 * n / total) if total else 0.0
    print(f"\nPROBLEM STATUS  (total {total} files)")
    print(f"{'─'*40}")
    print(f"  {'sat':12s}: {status_counts['sat']:5d}  ({pct(status_counts['sat']):.1f}%)")
    print(f"  {'unsat':12s}: {status_counts['unsat']:5d}  ({pct(status_counts['unsat']):.1f}%)")
    print(f"  {'unknown':12s}: {status_counts['unknown']:5d}  ({pct(status_counts['unknown']):.1f}%)")
    print(f"{'='*70}\n")

    # ── Optional CSV output ───────────────────────────────────────────────────
    if args.csv:
        import csv
        csv_path = Path(args.csv)
        fieldnames = ["file"] + SOLVER_NAMES + [f"t_{name}" for name in SOLVER_NAMES]
        fieldnames.extend(["category", "smtlib_status", "status"])
        for label in ext_names:
            fieldnames.extend([label, f"t_{label}"])
        with csv_path.open("w", newline="", encoding="utf-8") as f:
            writer = csv.DictWriter(f, fieldnames=fieldnames, extrasaction="ignore")
            writer.writeheader()
            for r in sorted(results, key=lambda x: x["file"]):
                writer.writerow({**r, "file": str(r["file"])})
        print(f"Results written to: {csv_path}")


if __name__ == "__main__":
    main()
