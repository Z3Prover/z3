---
name: prove
description: Prove validity of logical statements by negation and satisfiability checking. If the negation is unsatisfiable, the original statement is valid. Otherwise a counterexample is returned.
---

Given a conjecture (an SMT-LIB2 assertion or a natural language claim), determine whether it holds universally. The method is standard: negate the conjecture and check satisfiability. If the negation is unsatisfiable, the original is valid. If satisfiable, the model is a counterexample.

# Step 1: Prepare the negated formula

Action:
    Wrap the conjecture in `(assert (not ...))` and append
    `(check-sat)(get-model)`.

Expectation:
    A complete SMT-LIB2 formula that negates the original conjecture with
    all variables declared.

Result:
    If the negation is well-formed, proceed to Step 2.
    If the conjecture is natural language, run **encode** first.

Example: to prove that `(> x 3)` implies `(> x 1)`:
```smtlib
(declare-const x Int)
(assert (not (=> (> x 3) (> x 1))))
(check-sat)
(get-model)
```

# Step 2: Run the prover

Action:
    Invoke prove.py with the conjecture and variable declarations.

Expectation:
    The script prints `valid`, `invalid` (with counterexample), `unknown`,
    or `timeout`. A run entry is logged to z3agent.db.

Result:
    On `valid`: proceed to **explain** if the user needs a summary.
    On `invalid`: report the counterexample directly.
    On `unknown`/`timeout`: try **simplify** first, or increase the timeout.

```bash
python3 scripts/prove.py --conjecture "(=> (> x 3) (> x 1))" --vars "x:Int"
```

For file input where the file contains the full negated formula:
```bash
python3 scripts/prove.py --file negated.smt2
```

With debug tracing:
```bash
python3 scripts/prove.py --conjecture "(=> (> x 3) (> x 1))" --vars "x:Int" --debug
```

# Step 3: Interpret the output

Action:
    Read the prover output to determine validity of the conjecture.

Expectation:
    One of `valid`, `invalid` (with counterexample), `unknown`, or `timeout`.

Result:
    On `valid`: the conjecture holds universally.
    On `invalid`: the model shows a concrete counterexample.
    On `unknown`/`timeout`: the conjecture may require auxiliary lemmas or induction.

# Parameters

| Parameter | Type | Required | Default | Description |
|-----------|------|----------|---------|-------------|
| conjecture | string | no | | the assertion to prove (without negation) |
| vars | string | no | | variable declarations as "name:sort" pairs, comma-separated |
| file | path | no | | .smt2 file with the negated formula |
| timeout | int | no | 30 | seconds |
| z3 | path | no | auto | path to z3 binary |
| debug | flag | no | off | verbose tracing |
| db | path | no | .z3-agent/z3agent.db | logging database |

Either `conjecture` (with `vars`) or `file` must be provided.
