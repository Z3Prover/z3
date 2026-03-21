# nseq Solver Issues — Ostrich Benchmark Analysis

This directory contains GitHub issue drafts for the nseq solver based on analysis of
the Ostrich benchmark suite run on the c3 branch (Z3 v4.17.0, commit 8ef491e).

**Source**: https://github.com/Z3Prover/z3/discussions/9071  
**Branch**: c3  
**Benchmark set**: Ostrich (349 files), 5s timeout  
**Date**: 2026-03-21

## Summary of Results

| Solver | sat | unsat | unknown | timeout | bug/crash |
|--------|-----|-------|---------|---------|-----------|
| seq    | 242 | 75    | 28      | 0       | 4         |
| nseq   | 245 | 66    | 11      | 0       | 27        |

- **22 soundness disagreements** between seq and nseq (nseq returns sat where seq returns unsat in 11 cases)
- **27 nseq crashes** (vs 4 for seq, all on the same 4 parse-ecma files)
- **5+ performance regressions** (nseq timeout where seq solves in <30ms)

## Issue Files

### Soundness Bugs (Highest Priority)

1. **[01-soundness-replace-empty-string.md](01-soundness-replace-empty-string.md)**  
   `str.replace` with empty input returns sat instead of unsat.  
   Affects: `replace-special.smt2`, `replace-special-4.smt2`, `replace-special-5.smt2`, `simple-replace-4b.smt2`

2. **[02-soundness-contains-monotonicity.md](02-soundness-contains-monotonicity.md)**  
   `str.contains` not preserved through concatenation (`y ++ y`).  
   Affects: `contains-4.smt2`

3. **[03-soundness-indexof-regex.md](03-soundness-indexof-regex.md)**  
   `str.indexof` unsound when combined with regex membership constraints.  
   Affects: `indexof_const_index_unsat.smt2`, `indexof_var_unsat.smt2`

4. **[04-soundness-prefix-suffix.md](04-soundness-prefix-suffix.md)**  
   `str.prefixof` / `str.suffixof` interaction not fully axiomatized.  
   Affects: `prefix-suffix.smt2`, `failedProp.smt2`, `failedProp2.smt2`

5. **[05-soundness-conflicting-regex.md](05-soundness-conflicting-regex.md)**  
   Conflicting regex memberships not detected (disjoint character sets).  
   Affects: `norn-benchmark-9f.smt2`

### Crashes (Medium Priority)

6. **[06-crash-non-greedy-quantifiers.md](06-crash-non-greedy-quantifiers.md)**  
   Non-greedy regex quantifiers (`re.+?`, `re.*?`) cause crash.  
   Affects: `non-greedy-quantifiers.smt2`

7. **[07-crash-str-lt-le-axioms.md](07-crash-str-lt-le-axioms.md)**  
   `str.<` and `str.<=` axiom handling failures.  
   Affects: `str-leq11.smt2`, `str-leq12.smt2`, `str-leq13.smt2`, `str-lt.smt2`, `str-lt2.smt2`

8. **[08-crash-str-at-substr-from-to-int.md](08-crash-str-at-substr-from-to-int.md)**  
   Crashes on `str.at`, `str.substr`, `str.from_int`, `str.to_int` in complex formulas.  
   Affects: `str.at.smt2`, `str.at-2.smt2`, `str.from_int_6.smt2`, `str.to_int_5.smt2`, `str.to_int_6.smt2`, `substring.smt2`, `substring2.smt2`, `substring2b.smt2`, `is-digit-2.smt2`

9. **[09-crash-word-equation-regex.md](09-crash-word-equation-regex.md)**  
   Various crashes on word equation + regex benchmarks.  
   Affects: `concat-001.smt2`, `contains-1.smt2`, `contains-7.smt2`, `nonlinear-2.smt2`, `noodles-unsat8.smt2`, `noodles-unsat10.smt2`, `norn-benchmark-9i.smt2`, `pcp-1.smt2`

### Performance Regressions (Lower Priority)

10. **[10-performance-regression-regex-word-equation.md](10-performance-regression-regex-word-equation.md)**  
    nseq times out on regex + word equation benchmarks where seq is fast.  
    Affects: `concat-regex.smt2`, `concat-regex3.smt2`, `loop.smt2`, `simple-concat-4.smt2`, `all-quantifiers.smt2`

## Quick-Win Fixes

The following issues have clear, localized fixes:

1. **Non-greedy quantifiers** (issue 06): Add rewrite rules to normalize `re.+?` → `re.+`, `re.*?` → `re.*` in `seq_rewriter.cpp`.

2. **Boolean-equality pattern for contains** (issue 09, `contains-1.smt2`): In `assign_eh`, handle the pattern `(= (str.contains ...) true/false)` by extracting the inner predicate.

3. **Conflicting regex character sets** (issue 05): Improve the Parikh pre-check or add a character-set intersection check for multiple membership constraints on the same variable.
