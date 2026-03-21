# [nseq] Crash: non-greedy regex quantifiers (re.+?, re.*?) cause exception

**Labels**: bug, c3, nseq, crash

## Summary

The nseq solver crashes (throws an exception or returns an error) when the input
formula contains non-greedy regex quantifiers such as `re.+?` (lazy plus) or `re.*?`
(lazy star). The seq solver handles these correctly by treating them as equivalent to
their greedy counterparts for satisfiability purposes.

## Affected benchmark

| File | seq verdict | nseq verdict |
|------|-------------|--------------|
| `non-greedy-quantifiers.smt2` | sat | **bug/crash** |

Data from: https://github.com/Z3Prover/z3/discussions/9071

## Reproducing example

```smt2
; non-greedy-quantifiers.smt2 — EXPECTED: sat, nseq crashes
(set-logic QF_S)
(declare-fun a () String)
(declare-fun b () String)
(declare-fun c () String)
(declare-fun d () String)
(assert (= a (str.++ b c)))
(assert (= b (str.++ d c)))
; non-greedy re.+? has same semantics as re.+ for satisfiability
(assert (str.in.re a (re.+ (re.union (str.to.re "x") (str.to.re "y")))))
(assert (str.in.re c (re.+? (str.to.re "x"))))
(check-sat)
(get-model)
```

## Analysis

Z3's SMT-LIB parser supports non-greedy regex quantifiers (`re.+?`, `re.*?`, `re.??`)
as part of the ECMA-like regex extension. For satisfiability checking, non-greedy
quantifiers are semantically equivalent to their greedy counterparts (they only differ
in which match is returned, not in what strings are accepted).

The nseq solver's regex handling infrastructure (`seq_regex.cpp`) does not appear to
recognize or normalize non-greedy quantifiers. When the symbol `re.+?` is encountered
in a membership constraint, the solver either:
1. Does not recognize the operator and triggers `push_unhandled_pred()`, causing `FC_GIVEUP`
   (which may manifest as an error/"bug" in the benchmark runner), or
2. Crashes due to an unhandled case in the Brzozowski derivative computation or
   Parikh constraint generation.

### Fix proposal

Non-greedy quantifiers should be rewritten to their greedy equivalents before processing:
- `re.+? e` → `re.+ e` (lazy plus → greedy plus)
- `re.*? e` → `re.* e` (lazy star → greedy star)
- `re.?? e` → `re.opt e` (lazy optional → greedy optional)

This rewrite is sound for satisfiability/unsatisfiability since both interpretations
accept exactly the same language.

## Files to investigate

- `src/smt/seq/seq_regex.cpp` — regex preprocessing and derivative computation
- `src/ast/rewriter/seq_rewriter.cpp` — regex rewriting rules (add non-greedy normalization)
- `src/smt/theory_nseq.cpp` — `internalize_atom` / `assign_eh` for regex membership
