# TPTP Integration Test Report — `copilot/integrate-tptp-into-src-shell`

**Date:** 2026-05-12  
**Branch:** `copilot/integrate-tptp-into-src-shell`  
**Z3 version:** 4.17.0 (64-bit)  
**Test corpus:** 500 randomly-selected TPTP v8.1.2 problems  
**Domains sampled:** ARI (Arithmetic, n=247), SET (Set Theory, n=168), SYN (Syntactic, n=85)  
**Invocation:** `z3 -T:5 <file.p>`  

> **Note:** `tptp.org` was not accessible from the test sandbox (DNS blocked). Problems were drawn from the GoelandProver/GoelandBenchmarks repository, which mirrors TPTP v8.1.2 problem files in the same format.

---

## Executive Summary

| Category | Count | Pct |
|---|---|---|
| Correct answer | 178 | 35.6% |
| Wrong answer | 25 | 5.0% |
| Parse error - negative literal | 52 | 10.4% |
| Parse error - rational literal | 40 | 8.0% |
| Parse error - TFF type declaration | 96 | 19.2% |
| Sort mismatch (TFF arithmetic) | 46 | 9.2% |
| Crash (unhandled z3_error) | 40 | 8.0% |
| Timeout (process killed at 5s) | 23 | 4.6% |

**Overall correct rate: 178/500 = 35.6%**

---

## Timing

| Metric | Value |
|---|---|
| Minimum | 0.010 s |
| Maximum | 10.141 s |
| Mean | 1.099 s |
| Median | 0.029 s |
| Under 1 s | 435 (87.0%) |
| 1-5 s | 2 (0.4%) |
| Over 5 s | 63 (12.6%) |

---

## Per-Domain Results

| Domain | Correct | Total | Rate |
|---|---|---|---|
| ARI (Arithmetic) | 0 | 247 | 0.0% |
| SET (Set Theory) | 113 | 168 | 67.3% |
| SYN (Syntactic) | 65 | 85 | 76.5% |

---

## Bug Findings

### Bug 1 - Negative integer literals not parsed (52 files)

The TFF parser rejects negative integer literals such as `-2` or `-4`.

Example (ARI007_1.p):
```
tff(n2_less_2,conjecture, $less(-2,2) ).
```
Error: `TPTP parse error: unexpected character '-' at 32:11`

Every TFF problem using negative constants fails immediately.

---

### Bug 2 - Rational/real literals not parsed (40 files)

The parser rejects rational literals written as `p/q` (TPTP syntax for rationals, e.g. `1/2`).

Error pattern: `TPTP parse error: unexpected character '/' at 32:11`

---

### Bug 3 - TFF user-type declarations parse error (96 files)

TFF problems that introduce predicate or function type signatures fail to parse.

Example (ARI094_1.p):
```
tff(p_type,type, p: $int > $o ).
```
Error: `TPTP parse error: expected ')' at 32:19`

The `: $int > $o` type product syntax is not supported.

---

### Bug 4 - Sort mismatch for TFF typed variables (46 files)

When a TFF formula uses typed quantifier variables such as `[X: $int]`, the TPTP frontend binds them to the uninterpreted sort `U` rather than Z3's `Int` sort, causing a sort mismatch when they are passed to arithmetic built-ins.

Example (ARI005_1.p):
```
tff(prove_12_less_something,conjecture, ? [X: $int] : $less(12,X) ).
```
Error: `TPTP frontend error: Sort mismatch at argument #2 for function (declare-fun $less (U U) Bool) supplied sort: Int`

---

### Bug 5 - Arithmetic built-ins treated as uninterpreted (25 wrong answers)

Even when parsing succeeds, simple TFF arithmetic conjectures return CounterSatisfiable instead of Theorem. The arithmetic predicates `$less`, `$lesseq`, `$greater`, `$greatereq` are being declared as uninterpreted predicates over sort `U`, not mapped to Z3 built-in arithmetic relations.

Examples of wrong answers:
- ARI002_1.p: `~ $less(3,2)` → expected Theorem, got CounterSatisfiable
- ARI014_1.p: `$lesseq(2,2)` → expected Theorem, got CounterSatisfiable
- ARI015_1.p: `$less(2,3)` → expected Theorem, got CounterSatisfiable

---

### Bug 6 - Unhandled z3_error exception on timeout (40 crashes)

When a problem hits the timeout, Z3 crashes with:
```
terminate called after throwing an instance of 'z3_error'
  what():  timeout
```
instead of printing `% SZS status Timeout` and exiting cleanly. The TPTP frontend does not catch `z3_error` around the solver call.

---

## SET and SYN Domain (67-77% Success)

The SET and SYN domains use purely first-order FOF (untyped) formulas with no arithmetic and work reasonably well. Main failure modes are timeouts on harder combinatorial problems.

---

## Recommendations

1. Fix negative/rational literal parsing in the TPTP5 lexer
2. Map TFF arithmetic sorts ($int, $rat, $real) to Z3 Int/Real sorts
3. Map arithmetic predicates ($less, $lesseq, etc.) to Z3 built-in arithmetic relations
4. Support TFF type declaration syntax (name: sort > sort)
5. Catch z3_error in the TPTP frontend and output SZS Timeout status instead of crashing
