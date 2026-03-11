---
name: explain
description: Parse and interpret Z3 output for human consumption. Handles models, unsat cores, proofs, statistics, and error messages. Translates solver internals into plain-language explanations.
---

Given raw Z3 output (from the **solve**, **prove**, **optimize**, or **benchmark** skills), produce a structured explanation. This skill is for cases where the solver output is large, nested, or otherwise difficult to read directly.

# Step 1: Identify the output type

Action:
    Determine the category of Z3 output to explain: model, core,
    statistics, error, or proof.

Expectation:
    The output type maps to one of the recognized formats in the table below.

Result:
    If the type is ambiguous, use `--type auto` and let the script detect it.
    Proceed to Step 2.

| Output contains | Explanation type |
|----------------|-----------------|
| `(define-fun ...)` blocks | model explanation |
| unsat core labels | conflict explanation |
| `:key value` statistics | performance breakdown |
| `(error ...)` | error diagnosis |
| proof terms | proof sketch |

# Step 2: Run the explainer

Action:
    Invoke explain.py with the output file or stdin.

Expectation:
    The script auto-detects the output type and produces a structured
    plain-language summary.

Result:
    A formatted explanation is printed. If detection fails, re-run with
    an explicit `--type` flag.

```bash
python3 scripts/explain.py --file output.txt
python3 scripts/explain.py --stdin < output.txt
python3 scripts/explain.py --file output.txt --debug
```

# Step 3: Interpret the explanation

Action:
    Review the structured explanation for accuracy and completeness.

Expectation:
    Models list each variable with its value and sort. Cores list
    conflicting assertions. Statistics show time and memory breakdowns.

Result:
    Use the explanation to answer the user query or to guide the next
    skill invocation.

For models:
- Each variable is listed with its value and sort
- Array and function interpretations are expanded
- Bitvector values are shown in decimal and hex

For unsat cores:
- The conflicting named assertions are listed
- A minimal conflict set is highlighted

For statistics:
- Time breakdown by phase (preprocessing, solving, model construction)
- Theory solver load distribution
- Memory high-water mark

# Parameters

| Parameter | Type | Required | Default | Description |
|-----------|------|----------|---------|-------------|
| file | path | no | | file containing Z3 output |
| stdin | flag | no | off | read from stdin |
| type | string | no | auto | force output type: model, core, stats, error |
| debug | flag | no | off | verbose tracing |
| db | path | no | .z3-agent/z3agent.db | logging database |
