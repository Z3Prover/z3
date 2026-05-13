# TPTP Integration Test Report — `master` branch (re-run after #9483 merge)

**Date:** 2026-05-12
**Branch:** `master` (commit `1a2d3e0ebb` — "Integrate TPTP with internal APIs via `cmd_context`…")
**Z3 version:** 4.17.0 (64-bit)
**Test corpus:** 500 randomly-selected TPTP v8.1.2 problems (same seed=42 sample as previous run)
**Domains:** ARI (n=247), SET (n=168), SYN (n=85)
**Invocation:** `z3 -T:5 <file.p>`

> **Note:** `tptp.org` is not accessible from the CI sandbox. Problems are drawn from
> [GoelandProver/GoelandBenchmarks](https://github.com/GoelandProver/GoelandBenchmarks),
> which mirrors TPTP v8.1.2 in identical format.

---

## Results vs. Previous Run (`copilot/integrate-tptp-into-src-shell`)

| Category | Previous | Master | Change |
|---|---|---|---|
| Correct answer | 178 (35.6%) | 219 (43.8%) | +41 |
| Wrong answer | 25 (5.0%) | 15 (3.0%) | -10 |
| Parse error — negative literal | 52 (10.4%) | 0 (0.0%) | -52 |
| Parse error — rational literal | 40 (8.0%) | 0 (0.0%) | -40 |
| Parse error — TFF type declaration | 96 (19.2%) | 73 (14.6%) | -23 |
| Sort mismatch (TFF arithmetic) | 46 (9.2%) | 128 (25.6%) | +82 |
| Crash (unhandled z3_error) | 40 (8.0%) | 38 (7.6%) | -2 |
| Timeout (process killed at 5s) | 23 (4.6%) | 25 (5.0%) | +2 |
| Other errors | 0 (0.0%) | 2 (0.4%) | +2 |

**Overall correct rate: 219/500 = 43.8%** (was 35.6%)

---

## Per-Domain Accuracy

| Domain | Previous | Master |
|---|---|---|
| ARI (Arithmetic) | 0/247 (0.0%) | 43/247 (17.4%) |
| SET (Set Theory) | 113/168 (67.3%) | 113/168 (67.3%) |
| SYN (Syntactic) | 65/85 (76.5%) | 63/85 (74.1%) |

---

## Timing

| Metric | Value |
|---|---|
| Minimum | 0.008 s |
| Maximum | 10.169 s |
| Mean | 1.073 s |
| Median | 0.030 s |
| Under 1 s | 435 (87.0%) |
| Over 5 s | 63 (12.6%) |

---

## Fixes Confirmed in Master

### Fixed: Negative integer literals now parsed
`$less(-2, 2)` now returns `% SZS status Theorem` — **0 files** fail on negative literals (was 52).

### Fixed: Typed quantifier variables (`[X: $int]`)
`? [X: $int] : $less(12,X)` now returns `% SZS status Theorem` — resolved via correct sort mapping.

### Fixed: Simple arithmetic predicates as uninterpreted
The ARI domain went from **0% to 17.4%** correct. Simple facts like `$lesseq(2,2)` and `$less(2,3)` now return Theorem.

---

## Remaining Issues

### Issue 1 — Sort mismatch: bare integer constants treated as sort U (128 files)

When a TFF formula uses bare integer constants (no typed variables), the arithmetic constant is still in sort `U` instead of `Int`.

Example (`ARI055_1.p`):
```
tff(prove_31_not_12,conjecture, 31 != 12 ).
```
Error: `TPTP frontend error: Sorts U and Int are incompatible`

This is the most widespread remaining issue (128 files, 25.6%).

### Issue 2 — TFF type declarations not supported (73 files)

`tff(name, type, f: $int > $o)` type-introduction blocks still fail to parse.

Example (`ARI354_1.p`):
```
tff(real_less_problem_10,conjecture, ~ $less(-3.25,-8.69) ).
```
Error: `TPTP parse error: expected ')' at 32:15`

(The real literal `-3.25` triggers a different parse path than the negative integer `-2`.)

### Issue 3 — Real/rational literals with decimal point not parsed (73 files overlap)

Decimal real literals like `-3.25` or `1.5` are not recognized. These are a subset of the type-declaration parse errors.

### Issue 4 — `$uminus` function not recognized (2 files)

`$uminus(2)` is a TPTP arithmetic function for unary negation.
Error: `TPTP parse error: expected identifier at 32:5`

### Issue 5 — Crash on timeout (38 files)

Unchanged from before: when the timeout fires, `z3_error` is thrown uncaught and `std::terminate` is called, producing:
```
terminate called after throwing an instance of 'z3_error'
  what():  timeout
```
instead of `% SZS status Timeout`.

### Issue 6 — Wrong answers (15 files)

15 files receive an incorrect SZS verdict. Examples:
- `SYN364+1.p`, `SYN375+1.p`, `SYN377+1.p` — expected Theorem, got CounterSatisfiable
- `SET576+3.p` — expected Theorem, got CounterSatisfiable

These appear to be FOF problems in the SYN/SET domains where Z3's quantifier handling returns an incorrect model.

---

## Recommendations

1. **Fix bare integer constant sort** — when the formula context is TFF with `$int` typing, integer numeral tokens should produce `Int`-sorted terms, not `U`-sorted ones.
2. **Support decimal real literals** — add lexer support for `d.d` (decimal point) real literal syntax.
3. **Support `$uminus`** — map this TPTP arithmetic function to Z3's unary minus.
4. **Catch `z3_error` in TPTP frontend** — print `% SZS status Timeout` before exiting to avoid crashing.
