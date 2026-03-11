---
name: encode
description: Translate constraint problems into SMT-LIB2 or Z3 Python API code. Handles common problem classes including scheduling, graph coloring, arithmetic puzzles, and verification conditions.
---

Given a problem description (natural language, pseudocode, or a partial formulation), produce a complete, syntactically valid SMT-LIB2 encoding or Z3 Python script. The encoding should declare all variables, assert all constraints, and include the appropriate check-sat / get-model commands.

# Step 1: Identify the problem class

Common encodings:

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

```bash
python3 scripts/encode.py --problem "Find integers x, y such that x^2 + y^2 = 25 and x > 0" --format smtlib2
python3 scripts/encode.py --problem "Schedule 4 tasks on 2 machines minimizing makespan" --format python
```

For `--format smtlib2`, the output is a complete .smt2 file ready for the **solve** skill.
For `--format python`, the output is a standalone Z3 Python script.

# Step 3: Validate the encoding

The script checks that the generated formula is syntactically valid by running a quick `z3 -in` parse check (no solving, just syntax). Parse errors are reported with the offending line.

# Parameters

| Parameter | Type | Required | Default | Description |
|-----------|------|----------|---------|-------------|
| problem | string | yes | | problem description |
| format | string | no | smtlib2 | output format: smtlib2 or python |
| output | path | no | stdout | write to file instead of stdout |
| validate | flag | no | on | run syntax check on the output |
| debug | flag | no | off | verbose tracing |
| db | path | no | .z3-agent/z3agent.db | logging database |
