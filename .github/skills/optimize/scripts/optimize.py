#!/usr/bin/env python3
"""
optimize.py: solve constrained optimization problems via Z3.

Usage:
    python optimize.py --file scheduling.smt2
    python optimize.py --formula "(declare-const x Int)..." --debug
"""

import argparse
import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent.parent.parent / "shared"))
from z3db import Z3DB, run_z3, parse_model, setup_logging


def main():
    parser = argparse.ArgumentParser(prog="optimize")
    parser.add_argument("--formula")
    parser.add_argument("--file")
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
    run_id = db.start_run("optimize", formula)

    result = run_z3(formula, z3_bin=args.z3, timeout=args.timeout, debug=args.debug)

    model = parse_model(result["stdout"]) if result["result"] == "sat" else None

    db.log_formula(run_id, formula, result["result"],
                   str(model) if model else None)
    db.finish_run(run_id, result["result"], result["duration_ms"],
                  result["exit_code"])

    print(result["result"])
    if model:
        for name, val in model.items():
            print(f"  {name} = {val}")

    db.close()
    sys.exit(0 if result["exit_code"] == 0 else 1)


if __name__ == "__main__":
    main()
