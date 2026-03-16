#!/usr/bin/env python3
"""
prove.py: prove validity by negation + satisfiability check.

Usage:
    python prove.py --conjecture "(=> (> x 3) (> x 1))" --vars "x:Int"
    python prove.py --file negated.smt2
"""

import argparse
import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent.parent.parent / "shared"))
from z3db import Z3DB, run_z3, parse_model, setup_logging


def build_formula(conjecture: str, vars_str: str) -> str:
    lines = []
    if vars_str:
        for v in vars_str.split(","):
            v = v.strip()
            name, sort = v.split(":")
            lines.append(f"(declare-const {name.strip()} {sort.strip()})")
    lines.append(f"(assert (not {conjecture}))")
    lines.append("(check-sat)")
    lines.append("(get-model)")
    return "\n".join(lines)


def main():
    parser = argparse.ArgumentParser(prog="prove")
    parser.add_argument("--conjecture", help="assertion to prove")
    parser.add_argument("--vars", help="variable declarations, e.g. 'x:Int,y:Bool'")
    parser.add_argument("--file", help="path to .smt2 file with negated formula")
    parser.add_argument("--timeout", type=int, default=30)
    parser.add_argument("--z3", default=None)
    parser.add_argument("--db", default=None)
    parser.add_argument("--debug", action="store_true")
    args = parser.parse_args()

    setup_logging(args.debug)

    if args.file:
        formula = Path(args.file).read_text()
    elif args.conjecture:
        formula = build_formula(args.conjecture, args.vars or "")
    else:
        parser.error("provide --conjecture or --file")
        return

    db = Z3DB(args.db)
    run_id = db.start_run("prove", formula)

    result = run_z3(formula, z3_bin=args.z3, timeout=args.timeout, debug=args.debug)

    if result["result"] == "unsat":
        verdict = "valid"
    elif result["result"] == "sat":
        verdict = "invalid"
    else:
        verdict = result["result"]

    model = parse_model(result["stdout"]) if verdict == "invalid" else None

    db.log_formula(run_id, formula, verdict, str(model) if model else None)
    db.finish_run(run_id, verdict, result["duration_ms"], result["exit_code"])

    print(verdict)
    if model:
        print("counterexample:")
        for name, val in model.items():
            print(f"  {name} = {val}")

    db.close()
    # Exit 0 when we successfully determined validity or invalidity;
    # exit 1 only for errors/timeouts.
    sys.exit(0 if verdict in ("valid", "invalid") else 1)


if __name__ == "__main__":
    main()
