---
name: simplify
description: Reduce formula complexity using Z3 tactic chains. Supports configurable tactic pipelines for boolean, arithmetic, and bitvector simplification.
---

Given a formula, apply a sequence of Z3 tactics to produce an equivalent but simpler form. This is useful for understanding what Z3 sees after preprocessing, debugging tactic selection, and reducing formula size before solving.

# Step 1: Choose tactics

Z3 provides dozens of tactics. Common ones:

| Tactic | What it does |
|--------|-------------|
| simplify | constant folding, algebraic identities |
| propagate-values | substitute known equalities |
| ctx-simplify | context-dependent simplification |
| elim-uncnstr | remove unconstrained variables |
| solve-eqs | Gaussian elimination |
| bit-blast | reduce bitvectors to booleans |
| tseitin-cnf | convert to CNF |
| aig | and-inverter graph reduction |

# Step 2: Run simplification

```bash
python3 scripts/simplify.py --formula "(assert (and (> x 0) (> x 0)))" --vars "x:Int"
python3 scripts/simplify.py --file formula.smt2 --tactics "simplify,propagate-values,ctx-simplify"
python3 scripts/simplify.py --file formula.smt2 --debug
```

Without `--tactics`, the script applies the default chain: `simplify`, `propagate-values`, `ctx-simplify`.

# Step 3: Interpret the output

The script prints the simplified formula in SMT-LIB2 syntax. Subgoals are printed as separate `(assert ...)` blocks.

# Parameters

| Parameter | Type | Required | Default | Description |
|-----------|------|----------|---------|-------------|
| formula | string | no | | SMT-LIB2 formula to simplify |
| vars | string | no | | variable declarations as "name:sort" pairs |
| file | path | no | | path to .smt2 file |
| tactics | string | no | simplify,propagate-values,ctx-simplify | comma-separated tactic names |
| timeout | int | no | 30 | seconds |
| z3 | path | no | auto | path to z3 binary |
| debug | flag | no | off | verbose tracing |
| db | path | no | .z3-agent/z3agent.db | logging database |
