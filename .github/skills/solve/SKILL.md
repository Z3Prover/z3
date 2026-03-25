---
name: solve
description: Check satisfiability of SMT-LIB2 formulas using Z3. Returns sat/unsat with models or unsat cores. Logs every invocation to z3agent.db for auditability.
---

Given an SMT-LIB2 formula (or a set of constraints described in natural language), determine whether the formula is satisfiable. If sat, extract a satisfying assignment. If unsat and tracking labels are present, extract the unsat core.

# Step 1: Prepare the formula

Action:
    Convert the input to valid SMT-LIB2. If the input is natural language,
    use the **encode** skill first.

Expectation:
    A syntactically valid SMT-LIB2 formula ending with `(check-sat)` and
    either `(get-model)` or `(get-unsat-core)` as appropriate.

Result:
    If valid SMT-LIB2 is ready, proceed to Step 2.
    If encoding is needed, run **encode** first and return here.

# Step 2: Run Z3

Action:
    Invoke solve.py with the formula string or file path.

Expectation:
    The script pipes the formula to `z3 -in`, logs the run to
    `.z3-agent/z3agent.db`, and prints the result.

Result:
    Output is one of `sat`, `unsat`, `unknown`, or `timeout`.
    Proceed to Step 3 to interpret.

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

# Step 3: Interpret the output

Action:
    Parse the Z3 output to determine satisfiability and extract any model
    or unsat core.

Expectation:
    `sat` with a model, `unsat` optionally with a core, `unknown`, or
    `timeout`.

Result:
    On `sat`: report the model to the user.
    On `unsat`: report the core if available.
    On `unknown`/`timeout`: try **simplify** or increase the timeout.

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
