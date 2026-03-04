#!/usr/bin/env python3
"""
Compare z3 string solvers: smt.string_solver=nseq (new) vs smt.string_solver=seq (old).

Usage:
    python compare_solvers.py <path-to-smtlib-files> [--ext .smt2]

Finds all .smt2 files under the given path, runs both solvers with a 5s timeout,
and reports:
  - Files where neither solver terminates (both timeout)
  - Files where only one solver terminates (and which one)
  - Files where both terminate
  - Files where results diverge (sat vs unsat)
"""

import argparse
import subprocess
import sys
import time
from concurrent.futures import ThreadPoolExecutor, as_completed
from pathlib import Path

Z3_BIN = r"C:\Users\Clemens\source\repos\z3-nseq\debug\z3"
TIMEOUT = 5  # seconds
COMMON_ARGS = ["model_validate=true"]

SOLVERS = {
    "nseq": "smt.string_solver=nseq",
    "seq":  "smt.string_solver=seq",
}


def run_z3(smt_file: Path, solver_arg: str) -> tuple[str, float]:
    """Run z3 on a file with the given solver argument.
    Returns (result, elapsed) where result is 'sat', 'unsat', 'unknown', or 'timeout'/'error'.
    """
    cmd = [Z3_BIN, solver_arg] + COMMON_ARGS + [str(smt_file)]
    start = time.monotonic()
    try:
        proc = subprocess.run(
            cmd,
            capture_output=True,
            text=True,
            timeout=TIMEOUT,
        )
        elapsed = time.monotonic() - start
        output = proc.stdout.strip()
        # Extract first meaningful line (sat/unsat/unknown)
        for line in output.splitlines():
            line = line.strip()
            if line in ("sat", "unsat", "unknown"):
                return line, elapsed
        return "unknown", elapsed
    except subprocess.TimeoutExpired:
        elapsed = time.monotonic() - start
        return "timeout", elapsed
    except Exception as e:
        elapsed = time.monotonic() - start
        return f"error:{e}", elapsed


def classify(res_nseq: str, res_seq: str) -> str:
    """Classify a pair of results into a category."""
    timed_nseq = res_nseq == "timeout"
    timed_seq  = res_seq  == "timeout"

    if timed_nseq and timed_seq:
        return "both_timeout"
    if timed_nseq:
        return "only_seq_terminates"
    if timed_seq:
        return "only_nseq_terminates"
    # Both terminated — check agreement
    if res_nseq == "unknown" or res_seq == "unknown":
        return "both_terminate_unknown_involved"
    if res_nseq == res_seq:
        return "both_agree"
    return "diverge"


def process_file(smt_file: Path) -> dict:
    res_nseq, t_nseq = run_z3(smt_file, SOLVERS["nseq"])
    res_seq,  t_seq  = run_z3(smt_file, SOLVERS["seq"])
    cat = classify(res_nseq, res_seq)
    return {
        "file":     smt_file,
        "nseq":     res_nseq,
        "seq":      res_seq,
        "t_nseq":   t_nseq,
        "t_seq":    t_seq,
        "category": cat,
    }


def main():
    parser = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    parser.add_argument("path", help="Directory containing SMT-LIB2 files")
    parser.add_argument("--ext", default=".smt2", help="File extension to search for (default: .smt2)")
    parser.add_argument("--jobs", type=int, default=4, help="Parallel workers (default: 4)")
    parser.add_argument("--csv", metavar="FILE", help="Also write results to a CSV file")
    args = parser.parse_args()

    root = Path(args.path)
    if not root.exists():
        print(f"Error: path does not exist: {root}", file=sys.stderr)
        sys.exit(1)

    files = sorted(root.rglob(f"*{args.ext}"))
    if not files:
        print(f"No {args.ext} files found under {root}", file=sys.stderr)
        sys.exit(1)

    print(f"Found {len(files)} files. Running with {args.jobs} parallel workers …\n")

    results = []
    with ThreadPoolExecutor(max_workers=args.jobs) as pool:
        futures = {pool.submit(process_file, f): f for f in files}
        done = 0
        for fut in as_completed(futures):
            done += 1
            r = fut.result()
            results.append(r)
            print(f"[{done:4d}/{len(files)}] {r['category']:35s}  nseq={r['nseq']:8s} ({r['t_nseq']:.1f}s)  "
                  f"seq={r['seq']:8s} ({r['t_seq']:.1f}s)  {r['file'].name}")

    # ── Summary ──────────────────────────────────────────────────────────────
    categories = {
        "both_timeout":                   [],
        "only_seq_terminates":            [],
        "only_nseq_terminates":           [],
        "both_agree":                     [],
        "both_terminate_unknown_involved":[],
        "diverge":                        [],
    }
    for r in results:
        categories.setdefault(r["category"], []).append(r)

    print("\n" + "="*70)
    print("SUMMARY")
    print("="*70)

    for cat, items in categories.items():
        if not items:
            continue
        print(f"\n{'─'*70}")
        print(f"  {cat.upper().replace('_', ' ')} ({len(items)} files)")
        print(f"{'─'*70}")
        for r in sorted(items, key=lambda x: x["file"]):
            print(f"  {r['file']}")
            if cat not in ("both_timeout", "both_agree"):
                print(f"    nseq={r['nseq']:8s} ({r['t_nseq']:.1f}s)   seq={r['seq']:8s} ({r['t_seq']:.1f}s)")

    print(f"\n{'='*70}")
    print(f"TOTALS")
    for cat, items in categories.items():
        print(f"  {cat:40s}: {len(items)}")
    print(f"{'='*70}\n")

    # ── Optional CSV output ───────────────────────────────────────────────────
    if args.csv:
        import csv
        csv_path = Path(args.csv)
        with csv_path.open("w", newline="", encoding="utf-8") as f:
            writer = csv.DictWriter(f, fieldnames=["file", "nseq", "seq", "t_nseq", "t_seq", "category"])
            writer.writeheader()
            for r in sorted(results, key=lambda x: x["file"]):
                writer.writerow({**r, "file": str(r["file"])})
        print(f"Results written to: {csv_path}")


if __name__ == "__main__":
    main()
