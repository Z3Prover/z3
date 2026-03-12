# Z3 Agent

A Copilot agent for the Z3 theorem prover. It wraps 9 skills that cover
SMT solving and code quality analysis.

## What it does

The agent handles two kinds of requests:

1. **SMT solving**: formulate constraints, check satisfiability, prove
   properties, optimize objectives, simplify expressions.
2. **Code quality**: run sanitizers (ASan, UBSan) and Clang Static Analyzer
   against the Z3 codebase to catch memory bugs and logic errors.

## Prerequisites

You need a built Z3 binary. The scripts look for it in this order:

1. Explicit `--z3 path/to/z3`
2. `build/z3`, `build/release/z3`, `build/debug/z3` (relative to repo root)
3. `z3` on your PATH

For code quality skills you also need:

- **memory-safety**: cmake, make, and a compiler with sanitizer support
  (gcc or clang). The script checks at startup and tells you what is missing.
- **static-analysis**: scan-build (part of clang-tools). Same early check
  with install instructions if absent.

## Using the agent in Copilot Chat

Mention `@z3` and describe what you want in plain language.
The agent figures out which skill to use, builds the formula if needed,
runs Z3, and gives you the result.

### solve: check satisfiability

```
@z3 is (x > 0 and y > 0 and x + y < 5) satisfiable over the integers?
```

Expected response: **sat** with a model like `x = 1, y = 1`.

```
@z3 can x + y = 10 and x - y = 4 both hold at the same time?
```

Expected response: **sat** with `x = 7, y = 3`.

```
@z3 is there an integer x where x > 0, x < 0?
```

Expected response: **unsat** (no such integer exists).

### prove: check if something is always true

```
@z3 prove that x * x >= 0 for all integers x
```

Expected response: **valid** (the negation is unsatisfiable, so the property holds).

```
@z3 is it true that (a + b)^2 >= 0 for all real a and b?
```

Expected response: **valid**.

```
@z3 prove that if x > y and y > z then x > z, for integers
```

Expected response: **valid** (transitivity of >).

### optimize: find the best value

```
@z3 maximize 3x + 2y where x >= 1, y >= 1, and x + y <= 20
```

Expected response: **sat** with `x = 19, y = 1` (objective = 59).

```
@z3 minimize x + y where x >= 5, y >= 3, and x + y >= 10
```

Expected response: **sat** with `x = 5, y = 5` or similar (objective = 10).

### simplify: reduce an expression

```
@z3 simplify x + 0 + 1*x
```

Expected response: `2*x`.

```
@z3 simplify (a and true) or (a and false)
```

Expected response: `a`.

### encode: translate a problem to SMT-LIB2

```
@z3 encode this as SMT-LIB2: find integers x and y where x + y = 10 and x > y
```

Expected response: the SMT-LIB2 formula:
```
(declare-const x Int)
(declare-const y Int)
(assert (= (+ x y) 10))
(assert (> x y))
(check-sat)
(get-model)
```

### explain: interpret Z3 output

```
@z3 what does this Z3 output mean?
sat
(
  (define-fun x () Int 7)
  (define-fun y () Int 3)
)
```

Expected response: a readable summary like "satisfying assignment: x = 7, y = 3".

```
@z3 Z3 returned unknown, what does that mean?
```

Expected response: an explanation of common causes (timeout, incomplete theory, quantifiers).

### benchmark: measure performance

```
@z3 how fast can Z3 solve (x > 0 and y > 0 and x + y < 100)? run it 5 times
```

Expected response: timing stats like min/median/max in milliseconds and the result.

### memory-safety: find memory bugs in Z3

```
@z3 run AddressSanitizer on the Z3 test suite
```

Expected response: builds Z3 with ASan, runs the tests, reports any findings
with category, file, and line number. If clean, reports no findings.

```
@z3 check for undefined behavior in Z3
```

Expected response: runs UBSan, same format.

```
@z3 run both sanitizers
```

Expected response: runs ASan and UBSan, aggregates findings from both.

### static-analysis: find bugs without running the code

```
@z3 run static analysis on the Z3 source
```

Expected response: runs Clang Static Analyzer, reports findings grouped by
category (null dereference, dead store, memory leak, etc.) with file and line.

### multi-skill: the agent chains skills when needed

```
@z3 prove that for all integers, if x^2 is even then x is even
```

The agent uses **encode** to formalize and negate the statement, then
**prove** to check it, then **explain** to present the result.

```
@z3 full verification pass before the release
```

The agent runs **memory-safety** (ASan + UBSan) and **static-analysis**
in parallel, then aggregates and deduplicates findings sorted by severity.

## Using the scripts directly

Every skill lives under `.github/skills/<name>/scripts/`. All scripts
accept `--debug` for full tracing and `--db path` to specify where the
SQLite log goes (defaults to `z3agent.db` in the current directory).

### solve

Check whether a set of constraints has a solution.

```
python3 .github/skills/solve/scripts/solve.py \
  --z3 build/release/z3 \
  --formula '
(declare-const x Int)
(declare-const y Int)
(assert (> x 0))
(assert (> y 0))
(assert (< (+ x y) 5))
(check-sat)
(get-model)'
```

Output:

```
sat
  x = 1
  y = 1
```

### prove

Check whether a property holds for all values. The script negates your
conjecture and asks Z3 if the negation is satisfiable. If it is not,
the property is valid.

```
python3 .github/skills/prove/scripts/prove.py \
  --z3 build/release/z3 \
  --conjecture '(>= (* x x) 0)' \
  --vars 'x:Int'
```

Output:

```
valid
```

If Z3 finds a counterexample, it prints `invalid` followed by the
counterexample values.

### optimize

Find the best value of an objective subject to constraints.

```
python3 .github/skills/optimize/scripts/optimize.py \
  --z3 build/release/z3 \
  --formula '
(declare-const x Int)
(declare-const y Int)
(assert (>= x 1))
(assert (>= y 1))
(assert (<= (+ x y) 20))
(maximize (+ (* 3 x) (* 2 y)))
(check-sat)
(get-model)'
```

Output:

```
sat
  x = 19
  y = 1
```

Here Z3 maximizes `3x + 2y` under the constraint `x + y <= 20`, so it
pushes x as high as possible (19) and keeps y at its minimum (1),
giving `3*19 + 2*1 = 59`.

### simplify

Reduce expressions using Z3 tactic chains.

```
python3 .github/skills/simplify/scripts/simplify.py \
  --z3 build/release/z3 \
  --formula '(declare-const x Int)(simplify (+ x 0 (* 1 x)))'
```

Output:

```
(* 2 x)
(goals
(goal
  :precision precise :depth 1)
)
```

Z3 simplified `x + 0 + 1*x` down to `2*x`.

### benchmark

Measure solving time over multiple runs.

```
python3 .github/skills/benchmark/scripts/benchmark.py \
  --z3 build/release/z3 \
  --runs 5 \
  --formula '
(declare-const x Int)
(declare-const y Int)
(assert (> x 0))
(assert (> y 0))
(assert (< (+ x y) 100))
(check-sat)'
```

Output (times will vary on your machine):

```
runs: 5
min: 27ms
median: 28ms
max: 30ms
result: sat
```

### explain

Interpret Z3 output in readable form. It reads from stdin:

```
echo 'sat
(
  (define-fun x () Int
    19)
  (define-fun y () Int
    1)
)' | python3 .github/skills/explain/scripts/explain.py --stdin --type model
```

Output:

```
satisfying assignment:
  x = 19
  y = 1
```

### encode

Validate that an SMT-LIB2 file is well-formed by running it through Z3:

```
python3 .github/skills/encode/scripts/encode.py \
  --z3 build/release/z3 \
  --validate problem.smt2
```

If the file parses and runs without errors, it prints the formula back.
If there are syntax or sort errors, it prints the Z3 error message.

### memory-safety

Build Z3 with AddressSanitizer or UndefinedBehaviorSanitizer, run the
test suite, and collect any findings.

```
python3 .github/skills/memory-safety/scripts/memory_safety.py --sanitizer asan
python3 .github/skills/memory-safety/scripts/memory_safety.py --sanitizer ubsan
python3 .github/skills/memory-safety/scripts/memory_safety.py --sanitizer both
```

Use `--skip-build` to reuse a previous instrumented build. Use
`--build-dir path` to control where the build goes (defaults to
`build/sanitizer-asan` or `build/sanitizer-ubsan` under the repo root).

If cmake, make, or a C compiler is not found, the script prints what
you need to install and exits.

### static-analysis

Run Clang Static Analyzer over the Z3 source tree.

```
python3 .github/skills/static-analysis/scripts/static_analysis.py \
  --build-dir build/scan
```

Results go to `build/scan/scan-results/` by default. Findings are
printed grouped by category with file and line number.

If `scan-build` is not on your PATH, the script prints install
instructions for Ubuntu, macOS, and Fedora.

## Debug tracing

Add `--debug` to any command to see the full trace: run IDs, z3 binary
path, the exact command and stdin sent to Z3, stdout/stderr received,
timing, and database logging. Example:

```
python3 .github/skills/solve/scripts/solve.py \
  --z3 build/release/z3 --debug \
  --formula '
(declare-const x Int)
(declare-const y Int)
(assert (> x 0))
(assert (> y 0))
(assert (< (+ x y) 5))
(check-sat)
(get-model)'
```

```
[DEBUG] started run 31 (skill=solve, hash=d64beb5a61842362)
[DEBUG] found z3: build/release/z3
[DEBUG] cmd: build/release/z3 -in
[DEBUG] stdin:
(declare-const x Int)
(declare-const y Int)
(assert (> x 0))
(assert (> y 0))
(assert (< (+ x y) 5))
(check-sat)
(get-model)
[DEBUG] exit_code=0 duration=28ms
[DEBUG] stdout:
sat
(
  (define-fun x () Int
    1)
  (define-fun y () Int
    1)
)
[DEBUG] finished run 31: sat (28ms)
sat
  x = 1
  y = 1
```

## Logging

Every run is logged to a SQLite database (`z3agent.db` by default).
You can query it directly:

```
sqlite3 z3agent.db "SELECT id, skill, status, duration_ms FROM runs ORDER BY id DESC LIMIT 10;"
```

Use `--db /path/to/file.db` on any script to put the database somewhere
else.

## Skill list

| Skill | What it does |
|-------|-------------|
| solve | check satisfiability, extract models or unsat cores |
| prove | prove validity by negating and checking unsatisfiability |
| optimize | minimize or maximize objectives under constraints |
| simplify | reduce formulas with Z3 tactic chains |
| encode | translate problems into SMT-LIB2, validate syntax |
| explain | interpret Z3 output (models, cores, stats, errors) |
| benchmark | measure solving time, collect statistics |
| memory-safety | run ASan/UBSan on Z3 test suite |
| static-analysis | run Clang Static Analyzer on Z3 source |
