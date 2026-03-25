#!/usr/bin/env python3
"""
simplify.py: apply Z3 tactics to simplify an SMT-LIB2 formula.

Usage:
    python simplify.py --formula "(assert (and (> x 0) (> x 0)))" --vars "x:Int"
    python simplify.py --file formula.smt2 --tactics "simplify,solve-eqs"
"""

import argparse
import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent.parent.parent / "shared"))
from z3db import Z3DB, run_z3, setup_logging

DEFAULT_TACTICS = "simplify,propagate-values,ctx-simplify"


def build_tactic_formula(base_formula: str, tactics: str) -> str:
    tactic_list = [t.strip() for t in tactics.split(",")]
    if len(tactic_list) == 1:
        tactic_expr = f"(then {tactic_list[0]} skip)"
    else:
        tactic_expr = "(then " + " ".join(tactic_list) + ")"
    return base_formula + f"\n(apply {tactic_expr})\n"


def build_formula_from_parts(formula_str: str, vars_str: str) -> str:
    lines = []
    if vars_str:
        for v in vars_str.split(","):
            v = v.strip()
            name, sort = v.split(":")
            lines.append(f"(declare-const {name.strip()} {sort.strip()})")
    lines.append(formula_str)
    return "\n".join(lines)


def main():
    parser = argparse.ArgumentParser(prog="simplify")
    parser.add_argument("--formula")
    parser.add_argument("--vars")
    parser.add_argument("--file")
    parser.add_argument("--tactics", default=DEFAULT_TACTICS)
    parser.add_argument("--timeout", type=int, default=30)
    parser.add_argument("--z3", default=None)
    parser.add_argument("--db", default=None)
    parser.add_argument("--debug", action="store_true")
    args = parser.parse_args()

    setup_logging(args.debug)

    if args.file:
        base = Path(args.file).read_text()
    elif args.formula:
        base = build_formula_from_parts(args.formula, args.vars or "")
    else:
        parser.error("provide --formula or --file")
        return

    formula = build_tactic_formula(base, args.tactics)

    db = Z3DB(args.db)
    run_id = db.start_run("simplify", formula)

    result = run_z3(formula, z3_bin=args.z3, timeout=args.timeout, debug=args.debug)

    status = "success" if result["exit_code"] == 0 else "error"
    db.log_formula(run_id, formula, status)
    db.finish_run(run_id, status, result["duration_ms"], result["exit_code"])

    print(result["stdout"])
    if result["stderr"] and result["exit_code"] != 0:
        print(result["stderr"], file=sys.stderr)

    db.close()
    sys.exit(0 if result["exit_code"] == 0 else 1)


if __name__ == "__main__":
    main()
