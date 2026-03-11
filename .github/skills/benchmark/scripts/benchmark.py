#!/usr/bin/env python3
"""
benchmark.py: measure Z3 performance with statistics.

Usage:
    python benchmark.py --file problem.smt2
    python benchmark.py --file problem.smt2 --runs 5
"""

import argparse
import statistics
import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent.parent.parent / "shared"))
from z3db import Z3DB, run_z3, parse_stats, setup_logging


def main():
    parser = argparse.ArgumentParser(prog="benchmark")
    parser.add_argument("--formula")
    parser.add_argument("--file")
    parser.add_argument("--runs", type=int, default=1)
    parser.add_argument("--timeout", type=int, default=60)
    parser.add_argument("--z3", default=None)
    parser.add_argument("--db", default=None)
    parser.add_argument("--debug", action="store_true")
    args = parser.parse_args()

    setup_logging(args.debug)

    if args.file:
        formula = Path(args.file).read_text()
    elif args.formula:
        formula = args.formula
    else:
        parser.error("provide --formula or --file")
        return

    db = Z3DB(args.db)
    timings = []

    for i in range(args.runs):
        run_id = db.start_run("benchmark", formula)
        result = run_z3(formula, z3_bin=args.z3, timeout=args.timeout,
                        args=["-st"], debug=args.debug)

        stats = parse_stats(result["stdout"])
        db.log_formula(run_id, formula, result["result"], stats=stats)
        db.finish_run(run_id, result["result"], result["duration_ms"],
                      result["exit_code"])
        timings.append(result["duration_ms"])

        if args.runs == 1:
            print(f"result: {result['result']}")
            print(f"time: {result['duration_ms']}ms")
            if stats:
                print("statistics:")
                for k, v in sorted(stats.items()):
                    print(f"  :{k} {v}")

    if args.runs > 1:
        print(f"runs: {args.runs}")
        print(f"min: {min(timings)}ms")
        print(f"median: {statistics.median(timings):.0f}ms")
        print(f"max: {max(timings)}ms")
        print(f"result: {result['result']}")

    db.close()
    sys.exit(0 if result["exit_code"] == 0 else 1)


if __name__ == "__main__":
    main()
