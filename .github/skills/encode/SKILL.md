---
name: encode
description: Translate constraint problems into SMT-LIB2 or Z3 Python API code. Handles common problem classes including scheduling, graph coloring, arithmetic puzzles, and verification conditions.
---

Given a problem description (natural language, pseudocode, or a partial formulation), produce a complete, syntactically valid SMT-LIB2 encoding or Z3 Python script. The encoding should declare all variables, assert all constraints, and include the appropriate check-sat / get-model commands.

# Step 1: Identify the problem class

Action:
    Determine the SMT theory and variable sorts required by the problem
    description.

Expectation:
    A clear mapping from the problem to one of the supported theories
    (LIA, LRA, QF_BV, etc.).

Result:
    If the theory is identified, proceed to Step 2. If the problem spans
    multiple theories, select the appropriate combined logic.

| Problem class | Theory | Typical sorts |
|---------------|--------|---------------|
| Integer arithmetic | LIA / NIA | Int |
| Real arithmetic | LRA / NRA | Real |
| Bitvector operations | QF_BV | (_ BitVec N) |
| Arrays and maps | QF_AX | (Array Int Int) |
| Strings and regex | QF_S | String, RegLan |
| Uninterpreted functions | QF_UF | custom sorts |
| Mixed theories | AUFLIA, etc. | combination |

# Step 2: Generate the encoding

Action:
    Invoke encode.py with the problem description and desired output format.

Expectation:
    The script produces a complete SMT-LIB2 file or Z3 Python script with
    all declarations, constraints, and check-sat commands.

Result:
    For `smtlib2` format: pass the output to **solve**.
    For `python` format: execute the script directly.
    Proceed to Step 3 for validation.

```bash
python3 scripts/encode.py --problem "Find integers x, y such that x^2 + y^2 = 25 and x > 0" --format smtlib2
python3 scripts/encode.py --problem "Schedule 4 tasks on 2 machines minimizing makespan" --format python
```

# Step 3: Validate the encoding

Action:
    The script runs a syntax check by piping the output through `z3 -in`
    in parse-only mode.

Expectation:
    No parse errors. If errors occur, the offending line is reported.

Result:
    On success: the encoding is ready for **solve**, **prove**, or **optimize**.
    On parse error: fix the reported line and re-run.

# Parameters

| Parameter | Type | Required | Default | Description |
|-----------|------|----------|---------|-------------|
| problem | string | yes | | problem description |
| format | string | no | smtlib2 | output format: smtlib2 or python |
| output | path | no | stdout | write to file instead of stdout |
| validate | flag | no | on | run syntax check on the output |
| debug | flag | no | off | verbose tracing |
| db | path | no | .z3-agent/z3agent.db | logging database |
