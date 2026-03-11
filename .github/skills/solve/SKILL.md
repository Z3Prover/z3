---
name: solve
description: Check satisfiability of SMT-LIB2 formulas using Z3. Returns sat/unsat with models or unsat cores. Logs every invocation to z3agent.db for auditability.
---

Given an SMT-LIB2 formula (or a set of constraints described in natural language), determine whether the formula is satisfiable. If sat, extract a satisfying assignment. If unsat and tracking labels are present, extract the unsat core.

# Step 1: Prepare the formula

If the input is already valid SMT-LIB2, use it directly. If it is a natural language description, use the **encode** skill first to produce SMT-LIB2.

The formula must include `(check-sat)` at the end. Append `(get-model)` for satisfiable queries or `(get-unsat-core)` when named assertions are used.

# Step 2: Run Z3

```bash
python3 scripts/solve.py --formula "(declare-const x Int)(assert (> x 0))(check-sat)(get-model)"
```

For file input:
```bash
python3 scripts/solve.py --file problem.smt2
```

With debug tracing:
```bash
python3 scripts/solve.py --file problem.smt2 --debug
```

The script pipes the formula to `z3 -in` via subprocess (no shell expansion), logs the run to `.z3-agent/z3agent.db`, and prints the result.

# Step 3: Interpret the output

- `sat` followed by a model: the formula is satisfiable; the model assigns concrete values to each declared constant.
- `unsat`: no assignment exists. If `(get-unsat-core)` was used, the conflicting named assertions are listed.
- `unknown`: Z3 could not decide within the timeout. Consider increasing the timeout or simplifying the formula.
- `timeout`: the process was killed after the deadline. Try the **simplify** skill to reduce complexity.

# Parameters

| Parameter | Type | Required | Default | Description |
|-----------|------|----------|---------|-------------|
| formula | string | no | | SMT-LIB2 formula as a string |
| file | path | no | | path to an .smt2 file |
| timeout | int | no | 30 | seconds before killing z3 |
| z3 | path | no | auto | explicit path to z3 binary |
| debug | flag | no | off | print z3 command, stdin, stdout, stderr, timing |
| db | path | no | .z3-agent/z3agent.db | path to the logging database |

Either `formula` or `file` must be provided.
