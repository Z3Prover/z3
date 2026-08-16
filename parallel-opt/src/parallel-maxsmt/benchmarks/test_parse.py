"""Plain-assertion regression checks for the benchmark parser."""
from __future__ import annotations

import json
from pathlib import Path

import z3

from parse import ParsedProblem, parse_file, parse_wcnf

ROOT = Path(__file__).resolve().parent


def _integer(value: z3.ExprRef) -> int:
    if z3.is_int_value(value):
        return value.as_long()
    if z3.is_rational_value(value) and value.denominator_as_long() == 1:
        return value.numerator_as_long()
    raise AssertionError(f"non-integral optimum: {value!r}")


def _solve(problem: ParsedProblem) -> int:
    opt = z3.Optimize(ctx=problem.context)
    opt.add(*problem.hard)
    objective = z3.Sum(
        [z3.If(formula, z3.IntVal(0, ctx=problem.context), z3.IntVal(weight, ctx=problem.context)) for formula, weight in problem.soft]
    )
    handle = opt.minimize(objective)
    assert opt.check() == z3.sat
    return _integer(opt.lower(handle))


def test_round_trips_every_generated_instance() -> None:
    manifest = json.loads((ROOT / "manifest.json").read_text(encoding="utf-8"))
    # The smoke tier is the deterministic 24-instance portfolio; round-tripping
    # the calibrated eval/hard tiers as well would parse tens of thousands of
    # clauses per instance for no extra parser coverage.
    smoke = [row for row in manifest if row.get("tier") == "smoke"]
    assert len(smoke) >= 20, len(smoke)
    for row in smoke:
        ctx = z3.Context()
        problem = parse_file(ROOT / row["path"], ctx=ctx)
        assert all(formula.ctx is ctx for formula in problem.hard)
        assert all(formula.ctx is ctx for formula, _weight in problem.soft)
        assert len(problem.hard) == row["nhard"], row
        assert len(problem.soft) == row["nsoft"], row
        assert sum(weight for _formula, weight in problem.soft) == row["total_soft_weight"], row
    print(f"round-tripped {len(smoke)} smoke instances")


def test_known_optima_on_mixed_families() -> None:
    manifest = json.loads((ROOT / "manifest.json").read_text(encoding="utf-8"))
    chosen = {}
    for row in manifest:
        if row.get("tier") == "smoke":
            chosen.setdefault(row["family"], row)
    assert len(chosen) >= 5, chosen.keys()
    for family, row in sorted(chosen.items()):
        assert row["known_optimum"] is not None, row
        problem = parse_file(ROOT / row["path"], ctx=z3.Context())
        actual = _solve(problem)
        assert actual == row["known_optimum"], (family, actual, row["known_optimum"])
        print(f"known optimum {family}: {actual}")


def test_tiers_present_and_calibrated_files_parse() -> None:
    manifest = json.loads((ROOT / "manifest.json").read_text(encoding="utf-8"))
    tiers = {row.get("tier") for row in manifest}
    assert {"smoke", "eval", "hard"} <= tiers, tiers
    eval_rows = [r for r in manifest if r.get("tier") == "eval"]
    hard_rows = [r for r in manifest if r.get("tier") == "hard"]
    assert len(eval_rows) >= 15, len(eval_rows)
    assert len(hard_rows) >= 5, len(hard_rows)
    assert len({r["family"] for r in eval_rows}) >= 5
    for row in eval_rows:
        assert row["known_optimum"] is not None, row
        assert row.get("measured_seconds") is not None, row
    for row in hard_rows:
        # hard = optimality not proven within the calibration timeout.
        assert row["known_optimum"] is None, row
        assert row.get("best_known_cost") is not None, row
    # Structural parse check on the calibrated instances (no solving).
    for row in eval_rows + hard_rows:
        problem = parse_file(ROOT / row["path"], ctx=z3.Context())
        assert len(problem.hard) == row["nhard"], row
        assert len(problem.soft) == row["nsoft"], row
    print(f"tiers ok: {len(eval_rows)} eval + {len(hard_rows)} hard parsed structurally")


def test_old_and_new_dimacs_and_public_files() -> None:
    # New-format hard marker and old p cnf/p wcnf are all supported.
    ctx = z3.Context()
    new = parse_wcnf("h 1 0\n1 -1 0\n", ctx=ctx)
    assert len(new.hard) == 1 and len(new.soft) == 1
    old_w = parse_wcnf("p wcnf 1 2 10\n10 1 0\n3 -1 0\n", ctx=ctx)
    assert len(old_w.hard) == 1 and old_w.soft[0][1] == 3
    old = parse_wcnf("p cnf 1 1\n1 0\n", ctx=ctx)
    assert len(old.hard) == 0 and old.soft[0][1] == 1
    public = [
        ROOT / "public/dpmaxsat_cat.wcnf",
        ROOT / "public/dpmaxsat_test.cnf",
        ROOT / "public/z3_maxsat_ex.smt",
    ]
    for path in public:
        problem = parse_file(path)
        assert problem.soft, path
    print("parsed new DIMACS, old p cnf, and all downloaded public instances")


def main() -> int:
    test_round_trips_every_generated_instance()
    test_known_optima_on_mixed_families()
    test_tiers_present_and_calibrated_files_parse()
    test_old_and_new_dimacs_and_public_files()
    print("ALL PARSE TESTS PASSED")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
