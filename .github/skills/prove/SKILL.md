---
name: prove
description: Prove validity of logical statements by negation and satisfiability checking. If the negation is unsatisfiable, the original statement is valid. Otherwise a counterexample is returned.
---

Given a conjecture (an SMT-LIB2 assertion or a natural language claim), determine whether it holds universally. The method is standard: negate the conjecture and check satisfiability. If the negation is unsatisfiable, the original is valid. If satisfiable, the model is a counterexample.

# Step 1: Prepare the negated formula

Wrap the conjecture in `(assert (not ...))` and append `(check-sat)(get-model)`.

Example: to prove that `(> x 3)` implies `(> x 1)`:
```smtlib
(declare-const x Int)
(assert (not (=> (> x 3) (> x 1))))
(check-sat)
(get-model)
```

# Step 2: Run the prover

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

- `valid`: the negation was unsat, so the conjecture holds for all inputs.
- `invalid` followed by a counterexample: the negation was sat; the model shows a concrete assignment where the conjecture fails.
- `unknown` or `timeout`: Z3 could not decide. The conjecture may require auxiliary lemmas or induction.

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
