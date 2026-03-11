---
name: optimize
description: Solve constrained optimization problems using Z3. Supports minimization and maximization of objective functions over integer, real, and bitvector domains.
---

Given a set of constraints and an objective function, find the optimal value. Z3 supports both hard constraints (must hold) and soft constraints (weighted preferences), as well as lexicographic multi-objective optimization.

# Step 1: Formulate the problem

The formula uses the `(minimize ...)` or `(maximize ...)` directives followed by `(check-sat)` and `(get-model)`.

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

```bash
python3 scripts/optimize.py --file scheduling.smt2
python3 scripts/optimize.py --formula "<inline smt-lib2>" --debug
```

# Step 3: Interpret the output

- `sat` with a model: the optimal assignment satisfying all constraints.
- `unsat`: the constraints are contradictory; no feasible solution exists.
- `unknown` or `timeout`: Z3 could not determine optimality.

The script prints the objective value and the satisfying assignment.

# Parameters

| Parameter | Type | Required | Default | Description |
|-----------|------|----------|---------|-------------|
| formula | string | no | | SMT-LIB2 formula with minimize/maximize |
| file | path | no | | path to .smt2 file |
| timeout | int | no | 60 | seconds |
| z3 | path | no | auto | path to z3 binary |
| debug | flag | no | off | verbose tracing |
| db | path | no | .z3-agent/z3agent.db | logging database |
