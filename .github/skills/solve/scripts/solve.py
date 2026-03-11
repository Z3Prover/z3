#!/usr/bin/env python3
"""
solve.py: check satisfiability of an SMT-LIB2 formula via Z3.

Usage:
    python solve.py --formula "(declare-const x Int)(assert (> x 0))(check-sat)(get-model)"
    python solve.py --file problem.smt2
    python solve.py --file problem.smt2 --debug --timeout 60
"""

import argparse
import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent.parent.parent / "shared"))
from z3db import Z3DB, run_z3, parse_model, parse_unsat_core, setup_logging


def main():
    parser = argparse.ArgumentParser(prog="solve")
    parser.add_argument("--formula", help="SMT-LIB2 formula string")
    parser.add_argument("--file", help="path to .smt2 file")
    parser.add_argument("--timeout", type=int, default=30)
    parser.add_argument("--z3", default=None, help="path to z3 binary")
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
    run_id = db.start_run("solve", formula)

    result = run_z3(formula, z3_bin=args.z3, timeout=args.timeout, debug=args.debug)

    model = parse_model(result["stdout"]) if result["result"] == "sat" else None
    core = parse_unsat_core(result["stdout"]) if result["result"] == "unsat" else None

    db.log_formula(run_id, formula, result["result"], str(model) if model else None)
    db.finish_run(run_id, result["result"], result["duration_ms"], result["exit_code"])

    print(result["result"])
    if model:
        for name, val in model.items():
            print(f"  {name} = {val}")
    if core:
        print("unsat core:", " ".join(core))
    if result["stderr"] and result["result"] == "error":
        print(result["stderr"], file=sys.stderr)

    db.close()
    sys.exit(0 if result["exit_code"] == 0 else 1)


if __name__ == "__main__":
    main()
