#!/usr/bin/env python3
"""Compare z3-noodler against this z3 build on a corpus of SMT-LIB2 regex benchmarks.

Runs every benchmark under each configured solver, records the verdict and wall
time, and reports:

  * how many benchmarks each configuration decides,
  * cross-solver disagreements (one says sat, another unsat) -- these are bugs
    in one of the solvers and are the most valuable output of this comparison,
  * violations of a benchmark's own (set-info :status ...) annotation.

Usage:
    noodler_bench.py --corpus <dir> --out results.csv [--timeout 10] [--jobs 4]

Binaries are taken from $Z3_BIN and $NOODLER_BIN unless --z3 / --noodler are given.
"""

from __future__ import annotations

import argparse
import concurrent.futures
import csv
import os
import re
import subprocess
import sys
import time
from pathlib import Path

STATUS_RE = re.compile(r"\(\s*set-info\s+:status\s+(sat|unsat|unknown)\s*\)")
DECIDED = ("sat", "unsat")


def expected_status(path: Path) -> str:
    """The benchmark's own :status annotation, or '' when it carries none."""
    try:
        text = path.read_text(errors="replace")
    except OSError:
        return ""
    m = STATUS_RE.search(text)
    return m.group(1) if m else ""


def run_one(argv: list[str], path: Path, timeout: int) -> tuple[str, float]:
    """Run one solver on one file. Returns (verdict, milliseconds).

    The solver gets a soft -T: budget; the subprocess timeout is a hard backstop
    a few seconds later, for the case where the soft limit is not honoured.
    """
    start = time.perf_counter()
    try:
        proc = subprocess.run(
            argv + [str(path)],
            capture_output=True,
            text=True,
            timeout=timeout + 5,
        )
    except subprocess.TimeoutExpired:
        return "timeout", (time.perf_counter() - start) * 1000.0
    except OSError as e:
        return f"launch-error:{e.errno}", (time.perf_counter() - start) * 1000.0

    ms = (time.perf_counter() - start) * 1000.0
    out = (proc.stdout or "") + "\n" + (proc.stderr or "")
    verdict = "unknown"
    for raw in out.splitlines():
        line = raw.strip()
        if line in ("sat", "unsat"):
            verdict = line
            break
        if line == "unknown" or line == "timeout":
            verdict = "timeout" if line == "timeout" else "unknown"
            break
        if line.startswith("(error") or "Segmentation fault" in line:
            verdict = "error"
            break
    if verdict == "unknown" and proc.returncode not in (0, 1):
        verdict = f"crash:{proc.returncode}"
    return verdict, ms


def build_configs(z3: str, noodler: str, timeout: int) -> list[tuple[str, list[str]]]:
    """The three configurations under comparison.

    z3-noodler is a z3 fork, so it accepts the same -T: soft timeout flag.
    """
    t = [f"-T:{timeout}"]
    configs = []
    if noodler:
        configs.append(("noodler", [noodler] + t))
    configs.append(("z3-seq", [z3] + t))
    configs.append(("z3-monadic", [z3] + t + ["smt.seq.regex_monadic=true"]))
    return configs


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--corpus", required=True, type=Path)
    ap.add_argument("--out", required=True, type=Path)
    ap.add_argument("--timeout", type=int, default=10)
    ap.add_argument("--jobs", type=int, default=os.cpu_count() or 4)
    ap.add_argument("--limit", type=int, default=0,
                    help="sample only N benchmarks, spread evenly over the corpus")
    ap.add_argument("--z3", default=os.environ.get("Z3_BIN", "z3"))
    ap.add_argument("--noodler", default=os.environ.get("NOODLER_BIN", ""))
    ap.add_argument("--summary", type=Path, default=None,
                    help="write a markdown summary here (e.g. $GITHUB_STEP_SUMMARY)")
    args = ap.parse_args()

    if not args.corpus.is_dir():
        print(f"error: corpus directory not found: {args.corpus}", file=sys.stderr)
        return 2

    files = sorted(args.corpus.rglob("*.smt2"))
    if args.limit and args.limit < len(files):
        # Sample evenly rather than taking a prefix: the corpus is grouped into
        # families by directory, and a prefix would only ever cover the first.
        stride = len(files) / args.limit
        files = [files[int(i * stride)] for i in range(args.limit)]
    if not files:
        print(f"error: no .smt2 files under {args.corpus}", file=sys.stderr)
        return 2

    configs = build_configs(args.z3, args.noodler, args.timeout)
    print(f"corpus  : {args.corpus}  ({len(files)} benchmarks)")
    print(f"timeout : {args.timeout}s   jobs: {args.jobs}")
    for name, argv in configs:
        print(f"config  : {name:12} {' '.join(argv)}")
    sys.stdout.flush()

    # One task per (file, config) so that a slow configuration cannot stall the others.
    tasks = [(f, name, argv) for f in files for name, argv in configs]
    results: dict[Path, dict[str, tuple[str, float]]] = {f: {} for f in files}

    done = 0
    started = time.perf_counter()
    with concurrent.futures.ThreadPoolExecutor(max_workers=args.jobs) as pool:
        futs = {
            pool.submit(run_one, argv, f, args.timeout): (f, name)
            for f, name, argv in tasks
        }
        for fut in concurrent.futures.as_completed(futs):
            f, name = futs[fut]
            results[f][name] = fut.result()
            done += 1
            if done % 250 == 0:
                print(f"  {done}/{len(tasks)}  ({time.perf_counter()-started:.0f}s)")
                sys.stdout.flush()

    names = [n for n, _ in configs]
    args.out.parent.mkdir(parents=True, exist_ok=True)
    with args.out.open("w", newline="", encoding="utf-8") as fh:
        w = csv.writer(fh)
        header = ["file", "expected"]
        for n in names:
            header += [f"{n}_verdict", f"{n}_ms"]
        w.writerow(header)
        for f in files:
            row = [str(f.relative_to(args.corpus)).replace("\\", "/"), expected_status(f)]
            for n in names:
                v, ms = results[f].get(n, ("missing", 0.0))
                row += [v, f"{ms:.1f}"]
            w.writerow(row)

    # ---- analysis -------------------------------------------------------
    solved = {n: 0 for n in names}
    total_ms = {n: 0.0 for n in names}
    families: dict[str, dict[str, int]] = {}
    fam_total: dict[str, int] = {}
    disagreements: list[str] = []
    wrong: list[str] = []
    for f in files:
        rel = str(f.relative_to(args.corpus)).replace("\\", "/")
        fam = rel.split("/")[0] if "/" in rel else "(root)"
        families.setdefault(fam, {n: 0 for n in names})
        fam_total[fam] = fam_total.get(fam, 0) + 1
        verdicts = {n: results[f].get(n, ("missing", 0.0))[0] for n in names}
        for n in names:
            v, ms = results[f].get(n, ("missing", 0.0))
            total_ms[n] += ms
            if v in DECIDED:
                solved[n] += 1
                families[fam][n] += 1
        decided = {n: v for n, v in verdicts.items() if v in DECIDED}
        if len(set(decided.values())) > 1:
            disagreements.append(
                f"{rel}: " + ", ".join(f"{n}={v}" for n, v in decided.items())
            )
        exp = expected_status(f)
        if exp in DECIDED:
            for n, v in decided.items():
                if v != exp:
                    wrong.append(f"{rel}: {n}={v} but :status {exp}")

    lines: list[str] = []
    lines.append(f"## noodler-bench: {len(files)} benchmarks, {args.timeout}s timeout\n")
    lines.append("| configuration | decided | % | total time (s) |")
    lines.append("|---|---:|---:|---:|")
    for n in names:
        pct = 100.0 * solved[n] / len(files)
        lines.append(f"| `{n}` | {solved[n]} | {pct:.1f}% | {total_ms[n]/1000:.0f} |")
    lines.append("")

    if len(families) > 1:
        lines.append("### by family\n")
        lines.append("| family | benchmarks | " + " | ".join(f"`{n}`" for n in names) + " |")
        lines.append("|---|---:|" + "---:|" * len(names))
        for fam in sorted(families):
            counts = " | ".join(str(families[fam][n]) for n in names)
            lines.append(f"| {fam} | {fam_total[fam]} | {counts} |")
        lines.append("")

    if disagreements:
        lines.append(f"### :rotating_light: {len(disagreements)} sat/unsat disagreements\n")
        lines.append("A disagreement means one of the solvers is unsound on that benchmark.\n")
        for d in disagreements[:50]:
            lines.append(f"- `{d}`")
        if len(disagreements) > 50:
            lines.append(f"- ... and {len(disagreements)-50} more (see the CSV artifact)")
        lines.append("")
    else:
        lines.append("### :white_check_mark: no sat/unsat disagreements between solvers\n")

    if wrong:
        lines.append(f"### :rotating_light: {len(wrong)} answers contradicting a `:status` annotation\n")
        for d in wrong[:50]:
            lines.append(f"- `{d}`")
        if len(wrong) > 50:
            lines.append(f"- ... and {len(wrong)-50} more (see the CSV artifact)")
        lines.append("")
    else:
        lines.append("### :white_check_mark: no answers contradict a `:status` annotation\n")

    report = "\n".join(lines)
    print()
    print(report)
    if args.summary:
        with args.summary.open("a", encoding="utf-8") as fh:
            fh.write(report + "\n")

    # Disagreements and wrong answers are reported, but do not fail the job: this
    # is a measurement workflow, and a noodler bug should not turn our CI red.
    return 0


if __name__ == "__main__":
    sys.exit(main())
