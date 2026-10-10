#!/usr/bin/env python3
"""Depth safety and conservative recovery for the optional field backends."""
import argparse
import json
import re
import subprocess


def run(z3, src, expected, *options):
    result = subprocess.run([z3, "-in", "-st", *options], input=src,
                            text=True, capture_output=True, timeout=15)
    answers = re.findall(r"^(sat|unsat|unknown)\s*$", result.stdout, re.M)
    assert result.returncode == 0 and "(error" not in result.stdout, result
    assert answers == [expected], result.stdout
    return {k: float(v) for k, v in re.findall(r":([a-z0-9-]+)\s+([0-9.]+)", result.stdout)}


def bit_pair(prime, width):
    lines = ["(set-logic QF_FF)", f"(define-sort F () (_ FiniteField {prime}))"]
    for side in ["a", "b"]:
        for bit in range(width):
            v = f"{side}{bit}"
            lines += [f"(declare-const {v} F)", f"(assert (= (ff.mul {v} {v}) {v}))"]
    sums = ["(ff.add " + " ".join(f"(ff.mul (as ff{2**i} F) {side}{i})"
                                  for i in range(width)) + ")" for side in ["a", "b"]]
    lines += [f"(assert (= {sums[0]} {sums[1]}))", "(assert (not (= a0 b0)))"]
    return "\n".join(lines) + "\n"


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--z3", required=True)
    z3 = parser.parse_args().z3
    head = "(set-logic QF_FF)\n(define-sort F () (_ FiniteField 257))\n(declare-const x F)\n"
    term = "x"
    lets = []
    for i in range(60000):
        lets.append(f"(let ((t{i} (ff.neg {term}))) ")
        term = f"t{i}"
    deep = head + "(assert (= " + "".join(lets) + term + ")" * len(lets) + " (as ff1 F)))\n(assert (not (= x (as ff0 F))))\n"
    run(z3, deep + "(check-sat)", "sat")
    run(z3, deep + "(check-sat-using ff-unique)", "unknown")

    # Even a compact one-term DAG can encode an exponential monomial degree.
    term = "x"
    lets = []
    for i in range(25):
        lets.append(f"(let ((t{i} (ff.mul {term} {term}))) ")
        term = f"t{i}"
    powers = head + "(assert (= " + "".join(lets) + term + ")" * len(lets) + " (as ff1 F)))\n(assert (not (= x (as ff0 F))))\n"
    run(z3, powers + "(check-sat-using ff-unique)", "unknown")

    # Work is bounded inside a single propagation node; exhaustion preserves
    # every assertion and is not an UNSAT conclusion or global cancellation.
    wide = bit_pair(2**521 - 1, 256)
    stats = run(z3, wide + "(check-sat-using ff-unique)", "unknown", "smt.ff.unique_work=1000")
    assert stats["ff-unique-work"] <= 1000 and stats["ff-unique-exhausted"] == 1, stats
    small = bit_pair(257, 6)
    run(z3, small + "(check-sat)", "unsat", "smt.ff.unique_work=0")
    run(z3, small + "(check-sat)", "unsat", "smt.ff.unique=false")
    run(z3, small + "(check-sat-using ff-unique)", "unsat", "smt.ff.unique_depth=4294967295")
    # Binary encodings are not injective across modular wrap-around: 0 = 7.
    run(z3, bit_pair(7, 3) + "(check-sat)", "sat")
    print(json.dumps({"depth": 60000, "checks": 8, "local_budget_recovery": True}))


if __name__ == "__main__":
    main()
