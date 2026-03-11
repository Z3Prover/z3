#!/usr/bin/env python3
"""
deeptest.py: generate and run stress tests for Z3.

Usage:
    python deeptest.py --strategy random --count 100
    python deeptest.py --strategy metamorphic --seed-file base.smt2
    python deeptest.py --strategy cross-theory --theories "LIA,BV" --debug
"""

import argparse
import logging
import random
import sys
import time
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent.parent.parent / "shared"))
from z3db import Z3DB, run_z3, setup_logging

log = logging.getLogger("deeptest")

# Sort and operator tables

THEORY_SORTS = {
    "LIA":  "Int",
    "Bool": "Bool",
    "BV":   "(_ BitVec 32)",
}

INT_ARITH = ["+", "-", "*"]
INT_CMP   = [">", "<", ">=", "<=", "="]
BV_ARITH  = ["bvadd", "bvsub", "bvand", "bvor", "bvxor"]
BV_CMP    = ["bvslt", "bvsgt", "bvsle", "bvsge", "="]

# Assertion generators (one per sort)


def _int_assertion(rng, vs):
    if len(vs) < 2:
        return f"(assert ({rng.choice(INT_CMP)} {vs[0]} {rng.randint(-10, 10)}))"
    a, b = rng.sample(vs, 2)
    return f"(assert ({rng.choice(INT_CMP)} ({rng.choice(INT_ARITH)} {a} {b}) {rng.randint(-10, 10)}))"


def _bool_assertion(rng, vs):
    if len(vs) == 1:
        return f"(assert {vs[0]})" if rng.random() < 0.5 else f"(assert (not {vs[0]}))"
    a, b = rng.sample(vs, 2)
    return f"(assert ({rng.choice(['and', 'or', '=>'])} {a} {b}))"


def _bv_assertion(rng, vs):
    lit = f"(_ bv{rng.randint(0, 255)} 32)"
    if len(vs) < 2:
        return f"(assert ({rng.choice(BV_CMP)} {vs[0]} {lit}))"
    a, b = rng.sample(vs, 2)
    return f"(assert ({rng.choice(BV_CMP)} ({rng.choice(BV_ARITH)} {a} {b}) {lit}))"


SORT_ASSERTION = {
    "Int":            _int_assertion,
    "Bool":           _bool_assertion,
    "(_ BitVec 32)":  _bv_assertion,
}


def _random_assertion(rng, vars_by_sort):
    """Pick a populated sort and emit one random assertion."""
    available = [s for s in vars_by_sort if vars_by_sort[s]]
    if not available:
        return None
    sort = rng.choice(available)
    return SORT_ASSERTION[sort](rng, vars_by_sort[sort])

# Formula generators


def gen_random_formula(rng, num_vars=5, num_assertions=5):
    """Random declarations, random assertions, single check-sat."""
    lines = []
    vars_by_sort = {}
    sorts = list(THEORY_SORTS.values())

    for i in range(num_vars):
        sort = rng.choice(sorts)
        name = f"v{i}"
        lines.append(f"(declare-const {name} {sort})")
        vars_by_sort.setdefault(sort, []).append(name)

    for _ in range(num_assertions):
        a = _random_assertion(rng, vars_by_sort)
        if a:
            lines.append(a)

    lines.append("(check-sat)")
    return "\n".join(lines)


def gen_metamorphic_variant(rng, base_formula):
    """Apply an equisatisfiable transformation to a formula.

    Transformations:
      tautology   : insert (assert true) before check-sat
      double_neg  : wrap one assertion body in double negation
      duplicate   : repeat an existing assertion
    """
    lines = base_formula.strip().split("\n")
    transform = rng.choice(["tautology", "double_neg", "duplicate"])
    assertion_idxs = [i for i, l in enumerate(lines)
                      if l.strip().startswith("(assert")]

    if transform == "tautology":
        pos = next((i for i, l in enumerate(lines) if "check-sat" in l),
                   len(lines))
        lines.insert(pos, "(assert true)")

    elif transform == "double_neg" and assertion_idxs:
        idx = rng.choice(assertion_idxs)
        body = lines[idx].strip()
        inner = body[len("(assert "):-1]
        lines[idx] = f"(assert (not (not {inner})))"

    elif transform == "duplicate" and assertion_idxs:
        idx = rng.choice(assertion_idxs)
        lines.insert(idx + 1, lines[idx])

    return "\n".join(lines)


def gen_cross_theory_formula(rng, theories, num_vars=4, num_assertions=6):
    """Combine variables from multiple theories with bridging constraints."""
    lines = []
    vars_by_sort = {}
    sorts = [THEORY_SORTS[t] for t in theories if t in THEORY_SORTS]
    if not sorts:
        sorts = list(THEORY_SORTS.values())

    for i in range(num_vars):
        sort = sorts[i % len(sorts)]
        name = f"v{i}"
        lines.append(f"(declare-const {name} {sort})")
        vars_by_sort.setdefault(sort, []).append(name)

    for _ in range(num_assertions):
        a = _random_assertion(rng, vars_by_sort)
        if a:
            lines.append(a)

    # Bridge Int and Bool when both present
    int_vs = vars_by_sort.get("Int", [])
    bool_vs = vars_by_sort.get("Bool", [])
    if int_vs and bool_vs:
        iv = rng.choice(int_vs)
        bv = rng.choice(bool_vs)
        lines.append(f"(assert (= {bv} (> {iv} 0)))")

    lines.append("(check-sat)")
    return "\n".join(lines)


def gen_incremental_formula(rng, num_frames=3, num_vars=4,
                            asserts_per_frame=3):
    """Push/pop sequence: all variables declared globally, assertions scoped."""
    lines = []
    vars_by_sort = {}
    sorts = list(THEORY_SORTS.values())

    for i in range(num_vars):
        sort = rng.choice(sorts)
        name = f"v{i}"
        lines.append(f"(declare-const {name} {sort})")
        vars_by_sort.setdefault(sort, []).append(name)

    for _ in range(num_frames):
        lines.append("(push 1)")
        for _ in range(asserts_per_frame):
            a = _random_assertion(rng, vars_by_sort)
            if a:
                lines.append(a)
        lines.append("(check-sat)")
        lines.append("(pop 1)")

    lines.append("(check-sat)")
    return "\n".join(lines)

# Anomaly detection


def classify_result(result):
    """Return an anomaly category string or None if the result looks normal."""
    if result["exit_code"] != 0 and result["result"] != "timeout":
        return "crash"
    if "assertion" in result["stderr"].lower():
        return "assertion_failure"
    if result["result"] == "error":
        return "error"
    return None

# Strategy runners


def run_random(args, rng, db, run_id):
    anomalies = 0
    for i in range(args.count):
        formula = gen_random_formula(rng, rng.randint(2, 8),
                                     rng.randint(1, 10))
        log.debug("formula %d:\n%s", i, formula)
        result = run_z3(formula, z3_bin=args.z3, timeout=args.timeout,
                        debug=args.debug)
        db.log_formula(run_id, formula, result["result"])

        cat = classify_result(result)
        if cat:
            anomalies += 1
            db.log_finding(
                run_id, cat,
                f"random formula #{i}: {cat} (exit={result['exit_code']})",
                severity="high" if cat == "crash" else "medium",
                details={"formula_index": i,
                         "exit_code": result["exit_code"],
                         "stderr": result["stderr"][:500]})
            log.warning("anomaly in formula %d: %s", i, cat)
    return anomalies


def run_metamorphic(args, rng, db, run_id):
    if args.seed_file:
        base = Path(args.seed_file).read_text()
    else:
        base = gen_random_formula(rng, num_vars=4, num_assertions=3)

    base_out = run_z3(base, z3_bin=args.z3, timeout=args.timeout,
                      debug=args.debug)
    base_status = base_out["result"]
    db.log_formula(run_id, base, base_status)
    log.info("base formula result: %s", base_status)

    if base_status not in ("sat", "unsat"):
        db.log_finding(run_id, "skip",
                       f"base formula not definite: {base_status}",
                       severity="info")
        return 0

    anomalies = 0
    for i in range(args.count):
        variant = gen_metamorphic_variant(rng, base)
        log.debug("variant %d:\n%s", i, variant)
        result = run_z3(variant, z3_bin=args.z3, timeout=args.timeout,
                        debug=args.debug)
        db.log_formula(run_id, variant, result["result"])

        cat = classify_result(result)
        if cat:
            anomalies += 1
            db.log_finding(
                run_id, cat,
                f"metamorphic variant #{i}: {cat}",
                severity="high",
                details={"variant_index": i,
                         "stderr": result["stderr"][:500]})
            log.warning("anomaly in variant %d: %s", i, cat)
            continue

        if result["result"] in ("sat", "unsat") \
                and result["result"] != base_status:
            anomalies += 1
            db.log_finding(
                run_id, "disagreement",
                f"variant #{i}: expected {base_status}, "
                f"got {result['result']}",
                severity="critical",
                details={"variant_index": i,
                         "expected": base_status,
                         "actual": result["result"]})
            log.warning("disagreement in variant %d: expected %s, got %s",
                        i, base_status, result["result"])
    return anomalies


def run_cross_theory(args, rng, db, run_id):
    theories = [t.strip() for t in args.theories.split(",")]
    anomalies = 0
    for i in range(args.count):
        formula = gen_cross_theory_formula(rng, theories,
                                           rng.randint(3, 8),
                                           rng.randint(2, 10))
        log.debug("cross-theory formula %d:\n%s", i, formula)
        result = run_z3(formula, z3_bin=args.z3, timeout=args.timeout,
                        debug=args.debug)
        db.log_formula(run_id, formula, result["result"])

        cat = classify_result(result)
        if cat:
            anomalies += 1
            db.log_finding(
                run_id, cat,
                f"cross-theory #{i} ({','.join(theories)}): {cat}",
                severity="high" if cat == "crash" else "medium",
                details={"formula_index": i, "theories": theories,
                         "exit_code": result["exit_code"],
                         "stderr": result["stderr"][:500]})
            log.warning("anomaly in cross-theory formula %d: %s", i, cat)
    return anomalies


def run_incremental(args, rng, db, run_id):
    anomalies = 0
    for i in range(args.count):
        num_frames = rng.randint(2, 6)
        formula = gen_incremental_formula(rng, num_frames)
        log.debug("incremental formula %d:\n%s", i, formula)
        result = run_z3(formula, z3_bin=args.z3, timeout=args.timeout,
                        debug=args.debug)
        db.log_formula(run_id, formula, result["result"])

        cat = classify_result(result)
        if cat:
            anomalies += 1
            db.log_finding(
                run_id, cat,
                f"incremental #{i} ({num_frames} frames): {cat}",
                severity="high" if cat == "crash" else "medium",
                details={"formula_index": i, "num_frames": num_frames,
                         "exit_code": result["exit_code"],
                         "stderr": result["stderr"][:500]})
            log.warning("anomaly in incremental formula %d: %s", i, cat)
    return anomalies


STRATEGIES = {
    "random":        run_random,
    "metamorphic":   run_metamorphic,
    "cross-theory":  run_cross_theory,
    "incremental":   run_incremental,
}

# Entry point


def main():
    parser = argparse.ArgumentParser(
        prog="deeptest",
        description="Generate and run stress tests for Z3.",
    )
    parser.add_argument("--strategy", choices=list(STRATEGIES),
                        default="random",
                        help="test generation strategy")
    parser.add_argument("--count", type=int, default=50,
                        help="number of formulas to generate")
    parser.add_argument("--seed", type=int, default=None,
                        help="random seed for reproducibility")
    parser.add_argument("--seed-file", default=None,
                        help="base .smt2 file for metamorphic strategy")
    parser.add_argument("--theories", default="LIA,BV",
                        help="comma-separated theories for cross-theory")
    parser.add_argument("--timeout", type=int, default=10,
                        help="per-formula Z3 timeout in seconds")
    parser.add_argument("--z3", default=None, help="path to z3 binary")
    parser.add_argument("--db", default=None, help="path to z3agent.db")
    parser.add_argument("--debug", action="store_true")
    args = parser.parse_args()

    setup_logging(args.debug)

    seed = args.seed if args.seed is not None else int(time.time())
    rng = random.Random(seed)
    log.info("seed: %d", seed)

    db = Z3DB(args.db)
    run_id = db.start_run(
        "deeptest",
        f"strategy={args.strategy} count={args.count} seed={seed}")

    t0 = time.monotonic()
    anomalies = STRATEGIES[args.strategy](args, rng, db, run_id)
    elapsed_ms = int((time.monotonic() - t0) * 1000)

    status = "success" if anomalies == 0 else "findings"
    db.finish_run(run_id, status, elapsed_ms)

    print(f"strategy:  {args.strategy}")
    print(f"seed:      {seed}")
    print(f"formulas:  {args.count}")
    print(f"anomalies: {anomalies}")
    print(f"elapsed:   {elapsed_ms}ms")

    db.close()
    sys.exit(1 if anomalies > 0 else 0)


if __name__ == "__main__":
    main()
