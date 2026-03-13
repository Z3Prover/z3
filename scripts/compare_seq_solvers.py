#!/usr/bin/env python3
"""
Compare z3 string solvers: smt.string_solver=nseq (new) vs smt.string_solver=seq (old),
and optionally against an external ZIPT solver.

Usage:
    python compare_solvers.py <path-to-smtlib-files> --z3 /path/to/z3 [--zipt /path/to/zipt] [--ext .smt2]

Finds all .smt2 files under the given path, runs the solvers with a configurable timeout,
and reports timeouts, divergences, and summary statistics.
"""

import argparse
import re
import subprocess
import sys
import time
from concurrent.futures import ThreadPoolExecutor, as_completed
from pathlib import Path

DEFAULT_TIMEOUT = 5  # seconds
COMMON_ARGS = ["model_validate=true"]

SOLVERS = {
    "nseq": ["smt.string_solver=nseq"],
    "nseq_np": ["smt.string_solver=nseq", "smt.nseq.parikh=false"],
    "seq":  ["smt.string_solver=seq"],
}


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


def determine_status(res_nseq: str, res_seq: str, smtlib_status: str) -> str:
    """Determine the ground-truth status of a problem.
    Priority: if both solvers agree on sat/unsat, use that; otherwise if one
    solver gives sat/unsat, use that; otherwise fall back to the SMT-LIB
    annotation; otherwise 'unknown'.
    """
    definite = {"sat", "unsat"}
    if res_nseq in definite and res_nseq == res_seq:
        return res_nseq
    if res_nseq in definite and res_seq not in definite:
        return res_nseq
    if res_seq in definite and res_nseq not in definite:
        return res_seq
    # Disagreement (sat vs unsat) — fall back to SMTLIB annotation
    if res_nseq in definite and res_seq in definite and res_nseq != res_seq:
        if smtlib_status in definite:
            return smtlib_status
        return "unknown"
    # Neither solver gave a definite answer
    if smtlib_status in definite:
        return smtlib_status
    return "unknown"


def _parse_result(output: str) -> str:
    """Extract the first sat/unsat/unknown line from solver output."""
    for line in output.splitlines():
        tok = line.strip().lower()
        if tok in ("sat", "unsat"):
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


def run_zipt(zipt_bin: str, smt_file: Path, timeout_s: int = DEFAULT_TIMEOUT) -> tuple[str, float]:
    """Run ZIPT on a file. Returns (result, elapsed)."""
    timeout_ms = timeout_s * 1000
    cmd = [zipt_bin, f"-t:{timeout_ms}", str(smt_file)]
    start = time.monotonic()
    try:
        proc = subprocess.run(cmd, capture_output=True, text=True,
                              timeout=timeout_s + 5)
        elapsed = time.monotonic() - start
        out = proc.stdout.strip()
        return _parse_result(out), elapsed
    except subprocess.TimeoutExpired:
        elapsed = time.monotonic() - start
        return "timeout", elapsed
    except Exception as e:
        elapsed = time.monotonic() - start
        return f"error:{e}", elapsed


def classify(res_nseq: str, res_seq: str, res_nseq_np: str | None = None) -> str:
    """Classify a pair of results into a category."""
    timed_nseq = res_nseq == "timeout"
    timed_seq  = res_seq  == "timeout"
    
    if res_nseq_np:
        timed_nseq_np = res_nseq_np == "timeout"
        if timed_nseq and timed_seq and timed_nseq_np: return "all_timeout"
        if not timed_nseq and not timed_seq and not timed_nseq_np:
            if res_nseq == "unknown" or res_seq == "unknown" or res_nseq_np == "unknown":
                return "all_terminate_unknown_involved"
            if res_nseq == res_seq == res_nseq_np: return "all_agree"
            return "diverge"

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


def process_file(z3_bin: str, smt_file: Path, timeout_s: int = DEFAULT_TIMEOUT,
                 zipt_bin: str | None = None, run_nseq_np: bool = False) -> dict:
    res_nseq, t_nseq = run_z3(z3_bin, smt_file, SOLVERS["nseq"], timeout_s)
    res_seq,  t_seq  = run_z3(z3_bin, smt_file, SOLVERS["seq"], timeout_s)
    
    res_nseq_np, t_nseq_np = None, None
    if run_nseq_np:
        res_nseq_np, t_nseq_np = run_z3(z3_bin, smt_file, SOLVERS["nseq_np"], timeout_s)

    cat = classify(res_nseq, res_seq, res_nseq_np)
    smtlib_status = read_smtlib_status(smt_file)
    status = determine_status(res_nseq, res_seq, smtlib_status)
    result = {
        "file":           smt_file,
        "nseq":           res_nseq,
        "seq":            res_seq,
        "t_nseq":         t_nseq,
        "t_seq":          t_seq,
        "category":       cat,
        "smtlib_status":  smtlib_status,
        "status":         status,
        "zipt":           None,
        "t_zipt":         None,
        "nseq_np":        res_nseq_np,
        "t_nseq_np":      t_nseq_np,
    }
    if zipt_bin:
        res_zipt, t_zipt = run_zipt(zipt_bin, smt_file, timeout_s)
        result["zipt"]   = res_zipt
        result["t_zipt"] = t_zipt
    return result


def main():
    parser = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    parser.add_argument("path", help="Directory containing SMT-LIB2 files")
    parser.add_argument("--z3", required=True, metavar="PATH", help="Path to z3 binary")
    parser.add_argument("--ext", default=".smt2", help="File extension to search for (default: .smt2)")
    parser.add_argument("--jobs", type=int, default=4, help="Parallel workers (default: 4)")
    parser.add_argument("--timeout", type=int, default=DEFAULT_TIMEOUT, metavar="SEC",
                        help=f"Per-solver timeout in seconds (default: {DEFAULT_TIMEOUT})")
    parser.add_argument("--zipt", metavar="PATH", default=None,
                        help="Path to ZIPT binary (optional; if omitted, ZIPT is not benchmarked)")
    parser.add_argument("--no-parikh", action="store_true",
                        help="Also run nseq with nseq.parikh=false")
    parser.add_argument("--csv", metavar="FILE", help="Also write results to a CSV file")
    args = parser.parse_args()

    z3_bin = args.z3
    zipt_bin = args.zipt
    timeout_s = args.timeout

    root = Path(args.path)
    if not root.exists():
        print(f"Error: path does not exist: {root}", file=sys.stderr)
        sys.exit(1)

    files = sorted(root.rglob(f"*{args.ext}"))
    if not files:
        print(f"No {args.ext} files found under {root}", file=sys.stderr)
        sys.exit(1)

    solvers_label = "nseq, seq"
    if args.no_parikh: solvers_label += ", nseq_np"
    if zipt_bin: solvers_label += ", zipt"
    print(f"Found {len(files)} files. Solvers: {solvers_label}. "
          f"Workers: {args.jobs}, timeout: {timeout_s}s\n")

    results = []
    with ThreadPoolExecutor(max_workers=args.jobs) as pool:
        futures = {pool.submit(process_file, z3_bin, f, timeout_s, zipt_bin, args.no_parikh): f for f in files}
        done = 0
        for fut in as_completed(futures):
            done += 1
            r = fut.result()
            results.append(r)
            np_part = ""
            if args.no_parikh:
                np_part = f"  nseq_np={r['nseq_np']:8s} ({r['t_nseq_np']:.1f}s)"
            zipt_part = ""
            if zipt_bin:
                zipt_part = f"  zipt={r['zipt']:8s} ({r['t_zipt']:.1f}s)"
            print(f"[{done:4d}/{len(files)}] {r['category']:35s}  nseq={r['nseq']:8s} ({r['t_nseq']:.1f}s)  "
                  f"seq={r['seq']:8s} ({r['t_seq']:.1f}s){np_part}{zipt_part}  {r['file'].name}")

    # ── Summary ──────────────────────────────────────────────────────────────
    categories = {
        "all_timeout":                    [],
        "both_timeout":                   [],
        "only_seq_terminates":            [],
        "only_nseq_terminates":           [],
        "both_agree":                     [],
        "both_terminate_unknown_involved":[],
        "all_terminate_unknown_involved":[],
        "all_agree":                      [],
        "diverge":                        [],
    }
    for r in results:
        categories.setdefault(r["category"], []).append(r)

    print("\n" + "="*70)
    print("TOTALS")
    for cat, items in categories.items():
        print(f"  {cat:40s}: {len(items)}")
    print(f"{'='*70}")

    # ── Per-solver timeout & divergence file lists ─────────────────────────
    nseq_timeouts = [r for r in results if r["nseq"] == "timeout"]
    seq_timeouts  = [r for r in results if r["seq"]  == "timeout"]
    both_to       = categories["both_timeout"]
    diverged      = categories["diverge"]

    def _print_file_list(label: str, items: list[dict]):
        print(f"\n{'─'*70}")
        print(f"  {label} ({len(items)} files)")
        print(f"{'─'*70}")
        for r in sorted(items, key=lambda x: x["file"]):
            print(f"  {r['file']}")

    if nseq_timeouts:
        _print_file_list("NSEQ TIMES OUT", nseq_timeouts)
    if seq_timeouts:
        _print_file_list("SEQ TIMES OUT", seq_timeouts)
    if zipt_bin:
        zipt_timeouts = [r for r in results if r["zipt"] == "timeout"]
        if zipt_timeouts:
            _print_file_list("ZIPT TIMES OUT", zipt_timeouts)
    if both_to:
        _print_file_list("BOTH Z3 SOLVERS TIME OUT", both_to)
    if zipt_bin:
        all_to = [r for r in results
                  if r["nseq"] == "timeout" and r["seq"] == "timeout" and r["zipt"] == "timeout"]
        if all_to:
            _print_file_list("ALL THREE TIME OUT", all_to)
    if diverged:
        _print_file_list("DIVERGE nseq vs seq (sat vs unsat)", diverged)
    if zipt_bin:
        definite = {"sat", "unsat"}
        zipt_diverged = [r for r in results
                         if r["zipt"] in definite
                         and ((r["nseq"] in definite and r["nseq"] != r["zipt"])
                              or (r["seq"] in definite and r["seq"] != r["zipt"]))]
        if zipt_diverged:
            _print_file_list("DIVERGE involving ZIPT", zipt_diverged)

    print()

    # ── Problem status statistics ────────────────────────────────────────────
    status_counts = {"sat": 0, "unsat": 0, "unknown": 0}
    for r in results:
        status_counts[r["status"]] = status_counts.get(r["status"], 0) + 1

    print(f"\nPROBLEM STATUS  (total {len(results)} files)")
    print(f"{'─'*40}")
    print(f"  {'sat':12s}: {status_counts['sat']:5d}  ({100*status_counts['sat']/len(results):.1f}%)")
    print(f"  {'unsat':12s}: {status_counts['unsat']:5d}  ({100*status_counts['unsat']/len(results):.1f}%)")
    print(f"  {'unknown':12s}: {status_counts['unknown']:5d}  ({100*status_counts['unknown']/len(results):.1f}%)")
    print(f"{'='*70}\n")

    # ── Optional CSV output ───────────────────────────────────────────────────
    if args.csv:
        import csv
        csv_path = Path(args.csv)
        fieldnames = ["file", "nseq", "seq"]
        if args.no_parikh:
            fieldnames.append("nseq_np")
        fieldnames.extend(["t_nseq", "t_seq"])
        if args.no_parikh:
            fieldnames.append("t_nseq_np")
        fieldnames.extend(["category", "smtlib_status", "status"])
        if zipt_bin:
            fieldnames.extend(["zipt", "t_zipt"])
        with csv_path.open("w", newline="", encoding="utf-8") as f:
            writer = csv.DictWriter(f, fieldnames=fieldnames, extrasaction="ignore")
            writer.writeheader()
            for r in sorted(results, key=lambda x: x["file"]):
                writer.writerow({**r, "file": str(r["file"])})
        print(f"Results written to: {csv_path}")


if __name__ == "__main__":
    main()
