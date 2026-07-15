---
name: optimize
description: Solve constrained optimization problems using Z3. Supports minimization and maximization of objective functions over integer, real, and bitvector domains.
---

Given a set of constraints and an objective function, find the optimal value. Z3 supports both hard constraints (must hold) and soft constraints (weighted preferences), as well as lexicographic multi-objective optimization.

# Step 1: Formulate the problem

Action:
    Write constraints and an objective using `(minimize ...)` or
    `(maximize ...)` directives, followed by `(check-sat)` and `(get-model)`.

Expectation:
    A valid SMT-LIB2 formula with at least one optimization directive and
    all variables declared.

Result:
    If the formula is well-formed, proceed to Step 2. For multi-objective
    problems, list directives in priority order for lexicographic optimization.

Example: minimize `x + y` subject to `x >= 1`, `y >= 2`, `x + y <= 10`:
```smtlib
(declare-const x Int)
(declare-const y Int)
(assert (>= x 1))
(assert (>= y 2))
(assert (<= (+ x y) 10))
(minimize (+ x y))
(check-sat)
(get-model)
```

# Step 2: Run the optimizer

Action:
    Invoke optimize.py with the formula or file path.

Expectation:
    The script prints `sat` with the optimal assignment, `unsat`, `unknown`,
    or `timeout`. A run entry is logged to z3agent.db.

Result:
    On `sat`: proceed to Step 3 to read the optimal values.
    On `unsat` or `timeout`: check constraints for contradictions or simplify.

```bash
python3 scripts/optimize.py --file scheduling.smt2
python3 scripts/optimize.py --formula "<inline smt-lib2>" --debug
```

# Step 3: Interpret the output

Action:
    Parse the objective value and satisfying assignment from the output.

Expectation:
    `sat` with a model containing the optimal value, `unsat` indicating
    infeasibility, or `unknown`/`timeout`.

Result:
    On `sat`: report the optimal value and assignment.
    On `unsat`: the constraints are contradictory, no feasible solution exists.
    On `unknown`/`timeout`: relax constraints or try **simplify**.

# Parameters

| Parameter | Type | Required | Default | Description |
|-----------|------|----------|---------|-------------|
| formula | string | no | | SMT-LIB2 formula with minimize/maximize |
| file | path | no | | path to .smt2 file |
| timeout | int | no | 60 | seconds |
| z3 | path | no | auto | path to z3 binary |
| debug | flag | no | off | verbose tracing |
| db | path | no | .z3-agent/z3agent.db | logging database |
