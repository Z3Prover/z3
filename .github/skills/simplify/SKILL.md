---
name: simplify
description: Reduce formula complexity using Z3 tactic chains. Supports configurable tactic pipelines for boolean, arithmetic, and bitvector simplification.
---

Given a formula, apply a sequence of Z3 tactics to produce an equivalent but simpler form. This is useful for understanding what Z3 sees after preprocessing, debugging tactic selection, and reducing formula size before solving.

# Step 1: Choose tactics

Action:
    Select a tactic chain from the available Z3 tactics based on the
    formula's theory.

Expectation:
    A comma-separated list of tactic names suitable for the formula domain.

Result:
    If unsure, use the default chain: `simplify,propagate-values,ctx-simplify`.
    For bitvector formulas, add `bit-blast`. Proceed to Step 2.

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

Action:
    Invoke simplify.py with the formula and optional tactic chain.

Expectation:
    The script applies each tactic in sequence and prints the simplified
    formula. A run entry is logged to z3agent.db.

Result:
    If the output is simpler, pass it to **solve** or **prove**.
    If unchanged, try a different tactic chain.

```bash
python3 scripts/simplify.py --formula "(assert (and (> x 0) (> x 0)))" --vars "x:Int"
python3 scripts/simplify.py --file formula.smt2 --tactics "simplify,propagate-values,ctx-simplify"
python3 scripts/simplify.py --file formula.smt2 --debug
```

Without `--tactics`, the script applies the default chain: `simplify`, `propagate-values`, `ctx-simplify`.

# Step 3: Interpret the output

Action:
    Read the simplified formula output in SMT-LIB2 syntax.

Expectation:
    One or more `(assert ...)` blocks representing equivalent subgoals.

Result:
    A smaller formula indicates successful reduction. Pass the result to
    **solve**, **prove**, or **optimize** as needed.

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
