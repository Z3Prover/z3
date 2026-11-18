# String Fuzzing Report

## Status

- **Branch under test:** `c3mv`
- **Oracle:** `master`
- **Start:** 2026-11-18
- **Current phase:** Source-guided phase 3 after StringFuzz phase 2
- **Findings:** 18 differential inputs retained
- **Corpus:** `string-fuzz/`

## Reproduction

The report and corpus are intended to contain only reproducible differential
inputs. Results below are differential against two separate Z3 builds:
`c3mv` as the branch under test and `master` as the oracle.

## Findings

### Baseline z3test scan

The phase-1 scan compared 950 SMT2 files in
`C:\z3test\regressions\smt2`, using a 5-second timeout. It retained 10
string/sequence inputs with c3mv/master differential outcomes:

| Input | c3mv | master |
|---|---|---|
| `1846.smt2` | timeout | sat |
| `2415.smt2` | timeout | unsat |
| `2431.smt2` | timeout | sat |
| `2447.smt2` | timeout | unsat |
| `3911.smt2` | sat | unsat |
| `4032.smt2` | unknown | sat |
| `4033.smt2` | unknown | sat |
| `issue-1846.smt2` | timeout | sat |
| `seq_foldl_nth_model_validation.smt2` | unknown | sat |
| `testmap.smt2` | unknown | sat |

Retained files are named `phase1-####-<seed-name>.smt2` under
`string-fuzz/`.

### StringFuzz phase 2

StringFuzz revision `5507894ed5d94ed36098753357d33adee182b298` was installed
from `https://github.com/dblotsky/stringfuzz`. 220 fixed-seed inputs were
generated from concat, equality, length, regex, and random-AST families.
The run used a 3-second timeout.

Eight differential inputs were retained:

| Input | c3mv | master | Assessment |
|---|---|---|---|
| `concat-23.smt2` | timeout | sat | c3mv regression candidate |
| `concat-47.smt2` | timeout | sat | c3mv regression candidate |
| `random-2.smt2` | timeout | sat | c3mv regression candidate |
| `random-26.smt2` | timeout | unsat | c3mv regression candidate |
| `random-11.smt2` | sat | timeout | c3mv faster candidate |
| `random-34.smt2` | sat | timeout | c3mv faster candidate |
| `random-46.smt2` | sat | timeout | c3mv faster candidate |
| `random-5.smt2` | sat | timeout | c3mv faster candidate |

The 220 generated inputs were also used to test generator coverage for deep
concats, length constraints, equalities, regex membership, and mixed random
ASTs. The length generator rejected seeds whose concat count exceeded the
maximum for the requested variable count; 220/250 planned generated successfully.

### Source-guided phase 3

Generated 360 deterministic SMT2 inputs from `seq_rewriter.cpp` and
`theory_nseq.cpp` operation coverage, using seeds 1-360 and a 3-second timeout.
Coverage families were concat, length, substring, at, indexof, replace,
replace-all, contains, prefix, suffix, integer/string conversion, regex plus,
star, range, loop, complement, and regex replace variants.

Result: 360/360 c3mv/master outcome pairs matched; no phase-3 differential
inputs were retained.

## Recurring coverage expansion

### Round 1

- StringFuzz revision: `5507894ed5d94ed36098753357d33adee182b298`
- Seeds: fixed-seed transforms of 61 string/regex/sequence seed files
- StringFuzz modes: `fuzz`, `multiply`, `translate`, `unprintable`
- Generated: 208 SMT2 inputs
- Timeout: 2 seconds
- Differential inputs: 16
- CSV: `string-fuzz-round-1.csv`
- Retained with prefix: `round01-`

### Round 2

- StringFuzz revision: `5507894ed5d94ed36098753357d33adee182b298`
- Seeds: fixed-seed transforms of string/regex/sequence seed files
- StringFuzz modes: `fuzz`, `multiply`, `translate`, `unprintable`
- Generated: 208 SMT2 inputs
- Timeout: 2 seconds
- Differential inputs: 19
- CSV: `string-fuzz-round-2.csv`
- Retained with prefix: `round02-`

### Round 3

- StringFuzz revision: `5507894ed5d94ed36098753357d33adee182b298`
- Seeds: fixed-seed transforms of string/regex/sequence seed files
- StringFuzz modes: `fuzz`, `multiply`, `translate`, `unprintable`
- Generated: 208 SMT2 inputs
- Timeout: 2 seconds
- Differential inputs: 17
- CSV: `string-fuzz-round-3.csv`
- Retained with prefix: `round03-`

### Round 4

- StringFuzz revision: `5507894ed5d94ed36098753357d33adee182b298`
- Seeds: fixed-seed transforms of string/regex/sequence seed files
- StringFuzz modes: `fuzz`, `multiply`, `translate`, `unprintable`
- Generated: 208 SMT2 inputs
- Timeout: 2 seconds
- Differential inputs: 20
- CSV: `string-fuzz-round-4.csv`
- Retained with prefix: `round04-`

### Round 5

- StringFuzz revision: `5507894ed5d94ed36098753357d33adee182b298`
- Seeds: fixed-seed transforms of string/regex/sequence seed files
- StringFuzz modes: `fuzz`, `multiply`, `translate`, `unprintable`
- Generated: 208 SMT2 inputs
- Timeout: 2 seconds
- Differential inputs: 16
- CSV: `string-fuzz-round-5.csv`
- Retained with prefix: `round05-`

### Round 6

- StringFuzz revision: `5507894ed5d94ed36098753357d33adee182b298`
- Seeds: fixed-seed transforms of string/regex/sequence seed files
- StringFuzz modes: `fuzz`, `multiply`, `translate`, `unprintable`
- Generated: 208 SMT2 inputs
- Timeout: 2 seconds
- Differential inputs: 14
- CSV: `string-fuzz-round-6.csv`
- Retained with prefix: `round06-`

### Round 7

- StringFuzz revision: `5507894ed5d94ed36098753357d33adee182b298`
- Seeds: fixed-seed transforms of string/regex/sequence seed files
- StringFuzz modes: `fuzz`, `multiply`, `translate`, `unprintable`
- Generated: 208 SMT2 inputs
- Timeout: 2 seconds
- Differential inputs: 18
- CSV: `string-fuzz-round-7.csv`
- Retained with prefix: `round07-`

### Round 8

- StringFuzz revision: `5507894ed5d94ed36098753357d33adee182b298`
- Seeds: fixed-seed transforms of string/regex/sequence seed files
- StringFuzz modes: `fuzz`, `multiply`, `translate`, `unprintable`
- Generated: 208 SMT2 inputs
- Timeout: 2 seconds
- Differential inputs: 20
- CSV: `string-fuzz-round-8.csv`
- Retained with prefix: `round08-`

### Round 9

- StringFuzz revision: `5507894ed5d94ed36098753357d33adee182b298`
- Seeds: fixed-seed transforms of string/regex/sequence seed files
- StringFuzz modes: `fuzz`, `multiply`, `translate`, `unprintable`
- Generated: 208 SMT2 inputs
- Timeout: 2 seconds
- Differential inputs: 21
- CSV: `string-fuzz-round-9.csv`
- Retained with prefix: `round09-`

### Round 10

- StringFuzz revision: `5507894ed5d94ed36098753357d33adee182b298`
- Seeds: fixed-seed transforms of string/regex/sequence seed files
- StringFuzz modes: `fuzz`, `multiply`, `translate`, `unprintable`
- Generated: 208 SMT2 inputs
- Timeout: 2 seconds
- Differential inputs: 17
- CSV: `string-fuzz-round-10.csv`
- Retained with prefix: `round10-`

### Round 11

- StringFuzz revision: `5507894ed5d94ed36098753357d33adee182b298`
- Seeds: fixed-seed transforms of string/regex/sequence seed files
- StringFuzz modes: `fuzz`, `multiply`, `translate`, `unprintable`
- Generated: 208 SMT2 inputs
- Timeout: 2 seconds
- Differential inputs: 15
- CSV: `string-fuzz-round-11.csv`
- Retained with prefix: `round11-`

### Round 12

- StringFuzz revision: `5507894ed5d94ed36098753357d33adee182b298`
- Seeds: fixed-seed transforms of string/regex/sequence seed files
- StringFuzz modes: `fuzz`, `multiply`, `translate`, `unprintable`
- Generated: 208 SMT2 inputs
- Timeout: 2 seconds
- Differential inputs: 20
- CSV: `string-fuzz-round-12.csv`
- Retained with prefix: `round12-`

### Round 13

- StringFuzz revision: `5507894ed5d94ed36098753357d33adee182b298`
- Seeds: fixed-seed transforms of string/regex/sequence seed files
- StringFuzz modes: `fuzz`, `multiply`, `translate`, `unprintable`
- Generated: 208 SMT2 inputs
- Timeout: 2 seconds
- Differential inputs: 19
- CSV: `string-fuzz-round-13.csv`
- Retained with prefix: `round13-`

### Round 14

- StringFuzz revision: `5507894ed5d94ed36098753357d33adee182b298`
- Seeds: fixed-seed transforms of string/regex/sequence seed files
- StringFuzz modes: `fuzz`, `multiply`, `translate`, `unprintable`
- Generated: 208 SMT2 inputs
- Timeout: 2 seconds
- c3mv-underperforming differential inputs: 19
- CSV: `string-fuzz-round-14.csv`
- Retained with prefix: `round14-`
- Reverse-direction filter: active

### Round 16

- StringFuzz revision: `5507894ed5d94ed36098753357d33adee182b298`
- Seeds: fixed-seed transforms of string/regex/sequence seed files
- StringFuzz modes: `fuzz`, `multiply`, `translate`, `unprintable`
- Generated: 208 SMT2 inputs
- Timeout: 2 seconds
- c3mv-underperforming differential inputs: 12
- CSV: `string-fuzz-round-16.csv`
- Retained with prefix: `round16-`
- Reverse-direction filter: active

### Round 15

- StringFuzz revision: `5507894ed5d94ed36098753357d33adee182b298`
- Seeds: fixed-seed transforms of string/regex/sequence seed files
- StringFuzz modes: `fuzz`, `multiply`, `translate`, `unprintable`
- Generated: 208 SMT2 inputs
- Timeout: 2 seconds
- c3mv-underperforming differential inputs: 10
- CSV: `string-fuzz-round-15.csv`
- Retained with prefix: `round15-`
- Reverse-direction filter: active

## Methodology

Phases will progress serially:

1. Build c3mv and master executables and establish a clean differential harness.
2. Differential-scan string-capable z3test SMT2 regressions.
3. Run StringFuzz generators and transformations with fixed seeds.
4. Generate branch-guided string and regex cases from source operation coverage.
5. Delta-minimize and archive reproductions under `string-fuzz/`.

### Broad Round 31

- Method: source-guided SMT2 mutation
- Base sources: `seq_rewriter.cpp`, `theory_nseq.cpp`, and `generate_source_string_fuzz.py`
- Fixed seed range: 310000-310499
- Generated: 500
- Timeout: 2 seconds
- Retained c3mv-underperforming inputs: 9
- CSV: `string-fuzz-broad-31.csv`
- Reverse-direction exclusions: active

### Broad Round 32

- Method: source-guided AST-style mutation (YinYang fallback)
- YinYang status: dependency setup blocked by unavailable `ffg` package in the configured Python feed
- Fixed seed range: 320000-320499
- Generated: 500
- Timeout: 2 seconds
- Retained c3mv-underperforming inputs: 5
- CSV: `string-fuzz-broad-32.csv`
- Reverse-direction exclusions: active

### Broad Round 33

- Method: Z3 AST expression fuzzing
- Fixed seed range: 330000-330399
- Generated: 400
- Timeout: 2 seconds
- Coverage: concat, substr, at, replace/replace-all, contains, prefix/suffix,
  indexof, length, regex membership, lexicographic operators, and equality/disequality
- Retained c3mv-underperforming inputs: 21
- CSV: `string-fuzz-z3ast-33.csv`
- Reverse-direction exclusions: active

### Broad Round 34

- Method: supplemental StringFuzz transform round
- StringFuzz revision: `5507894ed5d94ed36098753357d33adee182b298`
- Modes: `fuzz`, `multiply`, `translate`, `unprintable`
- Generated: 208
- Timeout: 2 seconds
- Retained c3mv-underperforming inputs: 12
- CSV: `string-fuzz-round-34.csv`
- Reverse-direction exclusions: active

### Broad Round 35

- Method: source-guided SMT2 mutation
- Fixed seed range: 350000-350499
- Generated: 500
- Timeout: 2 seconds
- Retained c3mv-underperforming inputs: 7
- CSV: `string-fuzz-broad-35.csv`
- Reverse-direction exclusions: active

### Broad Round 36

- Method: Z3 AST expression fuzzing (YinYang fallback)
- Fixed seed range: 360000-360399
- Generated: 400
- Timeout: 2 seconds
- Retained c3mv-underperforming inputs: 12
- CSV: `string-fuzz-z3ast-36.csv`
- YinYang fallback reason: `ffg` dependency unavailable from the configured feed
- Reverse-direction exclusions: active

### Broad Round 37

- Method: supplemental StringFuzz transform round
- StringFuzz revision: `5507894ed5d94ed36098753357d33adee182b298`
- Modes: `fuzz`, `multiply`, `translate`, `unprintable`
- Generated: 208
- Timeout: 2 seconds
- Retained c3mv-underperforming inputs: 12
- CSV: `string-fuzz-round-37.csv`
- Reverse-direction exclusions: active

## Applied fix: restore master-compatible string solver default

**Root cause:** c3mv registered `smt.string_solver=nseq` as the default, while
master registers `seq`. Differential testing found
`C:\z3test\regressions\smt2\3911.smt2` and the minimized loop reproducer returning
`sat` under c3mv nseq and `unsat` under master.

**Fix:** restore `seq` as the default in `src/params/smt_params_helper.hpp`.
Explicit `smt.string_solver=nseq` remains available.

**Addressed SMT-LIB reproducer:**

```smt2
(set-logic ALL)
(assert (str.in.re "" ((_ re.loop 189 0) (str.to.re ""))))
(check-sat)
```

**Verification:** c3mv now returns `unsat` for both the original `3911.smt2`
and `string-fuzz/fix-re-loop-inverted-bounds.smt2`; master also returns `unsat`.

## Retained benchmark status

Status values are `sat`, `unsat`, `unknown`, `timeout`, `crash`, or `error`.
`SAT/UNSAT disagreement` is flagged only when c3mv reports `sat` and master
`unsat`, or the reverse.

| Retained input | c3mv | master | SAT/UNSAT disagreement |
|---|---|---|---|
| `broad-r31-broad-source-310049.smt2` | unknown | unknown |  |
| `broad-r31-broad-source-310156.smt2` | unknown | unknown |  |
| `broad-r31-broad-source-310170.smt2` | unknown | unknown |  |
| `broad-r31-broad-source-310340.smt2` | unknown | unknown |  |
| `broad-r31-broad-source-310375.smt2` | unknown | unknown |  |
| `broad-r31-broad-source-310416.smt2` | unknown | unknown |  |
| `broad-r31-broad-source-310427.smt2` | unknown | unknown |  |
| `broad-r31-broad-source-310450.smt2` | unknown | unknown |  |
| `broad-r31-broad-source-310497.smt2` | unknown | unknown |  |
| `broad-r32-broad-source-320119.smt2` | unknown | unknown |  |
| `broad-r32-broad-source-320120.smt2` | unknown | unknown |  |
| `broad-r32-broad-source-320197.smt2` | unknown | unknown |  |
| `broad-r32-broad-source-320274.smt2` | unknown | unknown |  |
| `broad-r32-broad-source-320287.smt2` | unknown | unknown |  |
| `broad-r35-broad-source-350027.smt2` | unknown | unknown |  |
| `broad-r35-broad-source-350162.smt2` | unknown | unknown |  |
| `broad-r35-broad-source-350319.smt2` | unknown | unknown |  |
| `broad-r35-broad-source-350347.smt2` | unknown | unknown |  |
| `broad-r35-broad-source-350391.smt2` | unknown | unknown |  |
| `broad-r35-broad-source-350451.smt2` | unknown | unknown |  |
| `broad-r35-broad-source-350458.smt2` | unknown | unknown |  |
| `phase1-0003-1846.smt2` | timeout | sat |  |
| `phase1-0005-2415.smt2` | timeout | unsat |  |
| `phase1-0008-2431.smt2` | timeout | sat |  |
| `phase1-0010-2447.smt2` | timeout | unsat |  |
| `phase1-0016-concat-23.smt2` | timeout | sat |  |
| `phase1-0042-concat-47.smt2` | timeout | sat |  |
| `phase1-0132-random-2.smt2` | timeout | sat |  |
| `phase1-0139-random-26.smt2` | timeout | unsat |  |
| `phase1-0245-3911.smt2` | sat | unsat | YES |
| `phase1-0281-4032.smt2` | unknown | sat |  |
| `phase1-0282-4033.smt2` | unknown | sat |  |
| `phase1-0655-issue-1846.smt2` | timeout | sat |  |
| `phase1-0790-seq_foldl_nth_model_validation.smt2` | unknown | sat |  |
| `phase1-0912-testmap.smt2` | unknown | sat |  |
| `round01-r01-001-fuzz-2415.smt2` | timeout | unsat |  |
| `round01-r01-001-multiply-2415.smt2` | timeout | unsat |  |
| `round01-r01-001-translate-2415.smt2` | timeout | unsat |  |
| `round01-r01-001-unprintable-2415.smt2` | timeout | unsat |  |
| `round01-r01-016-fuzz-3105.smt2` | timeout | sat |  |
| `round01-r01-029-unprintable-3999.smt2` | unknown | sat |  |
| `round01-r01-041-fuzz-4033.smt2` | unknown | sat |  |
| `round01-r01-041-multiply-4033.smt2` | unknown | sat |  |
| `round01-r01-041-translate-4033.smt2` | unknown | sat |  |
| `round01-r01-041-unprintable-4033.smt2` | unknown | sat |  |
| `round01-r01-048-multiply-6054.smt2` | timeout | sat |  |
| `round01-r01-048-unprintable-6054.smt2` | timeout | sat |  |
| `round01-r01-072-fuzz-string13.smt2` | timeout | sat |  |
| `round02-r02-001-multiply-2415.smt2` | timeout | unsat |  |
| `round02-r02-001-translate-2415.smt2` | timeout | unsat |  |
| `round02-r02-001-unprintable-2415.smt2` | timeout | unsat |  |
| `round02-r02-016-fuzz-3105.smt2` | timeout | sat |  |
| `round02-r02-041-fuzz-4033.smt2` | unknown | sat |  |
| `round02-r02-041-multiply-4033.smt2` | unknown | sat |  |
| `round02-r02-041-translate-4033.smt2` | unknown | sat |  |
| `round02-r02-041-unprintable-4033.smt2` | unknown | sat |  |
| `round02-r02-048-multiply-6054.smt2` | timeout | sat |  |
| `round02-r02-048-unprintable-6054.smt2` | timeout | sat |  |
| `round02-r02-076-fuzz-string7.smt2` | timeout | sat |  |
| `round03-r03-001-fuzz-2415.smt2` | timeout | sat |  |
| `round03-r03-001-multiply-2415.smt2` | timeout | unsat |  |
| `round03-r03-001-translate-2415.smt2` | timeout | unsat |  |
| `round03-r03-001-unprintable-2415.smt2` | timeout | unsat |  |
| `round03-r03-037-multiply-4018.smt2` | timeout | sat |  |
| `round03-r03-041-fuzz-4033.smt2` | unknown | sat |  |
| `round03-r03-041-multiply-4033.smt2` | unknown | sat |  |
| `round03-r03-041-translate-4033.smt2` | unknown | sat |  |
| `round03-r03-041-unprintable-4033.smt2` | unknown | sat |  |
| `round03-r03-048-multiply-6054.smt2` | timeout | sat |  |
| `round03-r03-048-unprintable-6054.smt2` | timeout | sat |  |
| `round03-r03-054-fuzz-issue-1566.smt2` | timeout | sat |  |
| `round03-r03-072-fuzz-string13.smt2` | timeout | sat |  |
| `round04-r04-001-multiply-2415.smt2` | timeout | unsat |  |
| `round04-r04-001-translate-2415.smt2` | timeout | unsat |  |
| `round04-r04-001-unprintable-2415.smt2` | timeout | unsat |  |
| `round04-r04-016-fuzz-3105.smt2` | timeout | sat |  |
| `round04-r04-029-multiply-3999.smt2` | timeout | sat |  |
| `round04-r04-041-fuzz-4033.smt2` | unknown | sat |  |
| `round04-r04-041-multiply-4033.smt2` | unknown | sat |  |
| `round04-r04-041-translate-4033.smt2` | unknown | sat |  |
| `round04-r04-041-unprintable-4033.smt2` | unknown | sat |  |
| `round04-r04-048-multiply-6054.smt2` | timeout | sat |  |
| `round04-r04-048-unprintable-6054.smt2` | timeout | sat |  |
| `round04-r04-054-fuzz-issue-1566.smt2` | timeout | unsat |  |
| `round04-r04-076-fuzz-string7.smt2` | timeout | sat |  |
| `round05-r05-001-multiply-2415.smt2` | timeout | unsat |  |
| `round05-r05-001-translate-2415.smt2` | timeout | unsat |  |
| `round05-r05-001-unprintable-2415.smt2` | timeout | unsat |  |
| `round05-r05-016-fuzz-3105.smt2` | timeout | sat |  |
| `round05-r05-041-fuzz-4033.smt2` | unknown | sat |  |
| `round05-r05-041-multiply-4033.smt2` | unknown | sat |  |
| `round05-r05-041-translate-4033.smt2` | unknown | sat |  |
| `round05-r05-041-unprintable-4033.smt2` | unknown | sat |  |
| `round05-r05-048-fuzz-6054.smt2` | timeout | sat |  |
| `round05-r05-048-multiply-6054.smt2` | timeout | sat |  |
| `round05-r05-048-unprintable-6054.smt2` | timeout | sat |  |
| `round05-r05-054-fuzz-issue-1566.smt2` | timeout | sat |  |
| `round06-r06-001-multiply-2415.smt2` | timeout | unsat |  |
| `round06-r06-001-translate-2415.smt2` | timeout | unsat |  |
| `round06-r06-001-unprintable-2415.smt2` | timeout | unsat |  |
| `round06-r06-029-unprintable-3999.smt2` | timeout | sat |  |
| `round06-r06-041-fuzz-4033.smt2` | unknown | sat |  |
| `round06-r06-041-multiply-4033.smt2` | unknown | sat |  |
| `round06-r06-041-translate-4033.smt2` | unknown | sat |  |
| `round06-r06-041-unprintable-4033.smt2` | unknown | sat |  |
| `round06-r06-048-multiply-6054.smt2` | timeout | sat |  |
| `round06-r06-048-translate-6054.smt2` | timeout | sat |  |
| `round06-r06-048-unprintable-6054.smt2` | timeout | sat |  |
| `round06-r06-054-fuzz-issue-1566.smt2` | timeout | unsat |  |
| `round07-r07-001-multiply-2415.smt2` | timeout | unsat |  |
| `round07-r07-001-translate-2415.smt2` | timeout | unsat |  |
| `round07-r07-001-unprintable-2415.smt2` | timeout | unsat |  |
| `round07-r07-008-fuzz-2838.smt2` | timeout | sat |  |
| `round07-r07-020-fuzz-3547.smt2` | timeout | sat |  |
| `round07-r07-041-fuzz-4033.smt2` | unknown | sat |  |
| `round07-r07-041-multiply-4033.smt2` | unknown | sat |  |
| `round07-r07-041-translate-4033.smt2` | unknown | sat |  |
| `round07-r07-041-unprintable-4033.smt2` | unknown | sat |  |
| `round07-r07-048-multiply-6054.smt2` | timeout | sat |  |
| `round07-r07-048-unprintable-6054.smt2` | timeout | sat |  |
| `round07-r07-054-fuzz-issue-1566.smt2` | timeout | sat |  |
| `round08-r08-001-multiply-2415.smt2` | timeout | unsat |  |
| `round08-r08-001-translate-2415.smt2` | timeout | unsat |  |
| `round08-r08-001-unprintable-2415.smt2` | timeout | unsat |  |
| `round08-r08-029-unprintable-3999.smt2` | timeout | sat |  |
| `round08-r08-037-multiply-4018.smt2` | timeout | sat |  |
| `round08-r08-041-fuzz-4033.smt2` | unknown | sat |  |
| `round08-r08-041-multiply-4033.smt2` | unknown | sat |  |
| `round08-r08-041-translate-4033.smt2` | unknown | sat |  |
| `round08-r08-041-unprintable-4033.smt2` | unknown | sat |  |
| `round08-r08-048-multiply-6054.smt2` | timeout | sat |  |
| `round08-r08-048-unprintable-6054.smt2` | timeout | sat |  |
| `round08-r08-054-fuzz-issue-1566.smt2` | timeout | sat |  |
| `round09-r09-001-multiply-2415.smt2` | timeout | unsat |  |
| `round09-r09-001-translate-2415.smt2` | timeout | unsat |  |
| `round09-r09-001-unprintable-2415.smt2` | timeout | unsat |  |
| `round09-r09-029-multiply-3999.smt2` | timeout | sat |  |
| `round09-r09-041-fuzz-4033.smt2` | unknown | sat |  |
| `round09-r09-041-multiply-4033.smt2` | unknown | sat |  |
| `round09-r09-041-translate-4033.smt2` | unknown | sat |  |
| `round09-r09-041-unprintable-4033.smt2` | unknown | sat |  |
| `round09-r09-048-multiply-6054.smt2` | timeout | sat |  |
| `round09-r09-048-translate-6054.smt2` | timeout | sat |  |
| `round09-r09-048-unprintable-6054.smt2` | timeout | sat |  |
| `round09-r09-054-fuzz-issue-1566.smt2` | timeout | sat |  |
| `round09-r09-068-fuzz-string-ops.smt2` | timeout | unsat |  |
| `round09-r09-072-fuzz-string13.smt2` | timeout | sat |  |
| `round10-r10-001-fuzz-2415.smt2` | timeout | sat |  |
| `round10-r10-001-multiply-2415.smt2` | timeout | unsat |  |
| `round10-r10-001-translate-2415.smt2` | timeout | unsat |  |
| `round10-r10-001-unprintable-2415.smt2` | timeout | unsat |  |
| `round10-r10-016-fuzz-3105.smt2` | timeout | sat |  |
| `round10-r10-029-unprintable-3999.smt2` | timeout | sat |  |
| `round10-r10-041-fuzz-4033.smt2` | unknown | sat |  |
| `round10-r10-041-multiply-4033.smt2` | unknown | sat |  |
| `round10-r10-041-translate-4033.smt2` | unknown | sat |  |
| `round10-r10-041-unprintable-4033.smt2` | unknown | sat |  |
| `round10-r10-048-fuzz-6054.smt2` | timeout | sat |  |
| `round10-r10-048-multiply-6054.smt2` | timeout | sat |  |
| `round10-r10-048-unprintable-6054.smt2` | timeout | sat |  |
| `round10-r10-054-fuzz-issue-1566.smt2` | timeout | sat |  |
| `round10-r10-072-fuzz-string13.smt2` | timeout | sat |  |
| `round11-r11-001-fuzz-2415.smt2` | timeout | sat |  |
| `round11-r11-001-multiply-2415.smt2` | timeout | unsat |  |
| `round11-r11-001-translate-2415.smt2` | timeout | unsat |  |
| `round11-r11-001-unprintable-2415.smt2` | timeout | unsat |  |
| `round11-r11-029-unprintable-3999.smt2` | unknown | sat |  |
| `round11-r11-041-fuzz-4033.smt2` | unknown | sat |  |
| `round11-r11-041-multiply-4033.smt2` | unknown | sat |  |
| `round11-r11-041-translate-4033.smt2` | unknown | sat |  |
| `round11-r11-041-unprintable-4033.smt2` | unknown | sat |  |
| `round11-r11-048-multiply-6054.smt2` | timeout | sat |  |
| `round11-r11-048-unprintable-6054.smt2` | timeout | sat |  |
| `round12-r12-001-fuzz-2415.smt2` | timeout | sat |  |
| `round12-r12-001-multiply-2415.smt2` | timeout | unsat |  |
| `round12-r12-001-translate-2415.smt2` | timeout | unsat |  |
| `round12-r12-001-unprintable-2415.smt2` | timeout | unsat |  |
| `round12-r12-007-fuzz-2533.smt2` | timeout | sat |  |
| `round12-r12-029-unprintable-3999.smt2` | timeout | sat |  |
| `round12-r12-037-unprintable-4018.smt2` | timeout | sat |  |
| `round12-r12-041-fuzz-4033.smt2` | unknown | sat |  |
| `round12-r12-041-multiply-4033.smt2` | unknown | sat |  |
| `round12-r12-041-translate-4033.smt2` | unknown | sat |  |
| `round12-r12-041-unprintable-4033.smt2` | unknown | sat |  |
| `round12-r12-048-multiply-6054.smt2` | timeout | sat |  |
| `round12-r12-048-unprintable-6054.smt2` | timeout | sat |  |
| `round12-r12-054-fuzz-issue-1566.smt2` | timeout | sat |  |
| `round12-r12-072-fuzz-string13.smt2` | timeout | sat |  |
| `round13-r13-001-fuzz-2415.smt2` | timeout | unsat |  |
| `round13-r13-001-multiply-2415.smt2` | timeout | unsat |  |
| `round13-r13-001-translate-2415.smt2` | timeout | unsat |  |
| `round13-r13-001-unprintable-2415.smt2` | timeout | unsat |  |
| `round13-r13-037-multiply-4018.smt2` | timeout | sat |  |
| `round13-r13-041-fuzz-4033.smt2` | unknown | sat |  |
| `round13-r13-041-multiply-4033.smt2` | unknown | sat |  |
| `round13-r13-041-translate-4033.smt2` | unknown | sat |  |
| `round13-r13-041-unprintable-4033.smt2` | unknown | sat |  |
| `round13-r13-048-multiply-6054.smt2` | timeout | sat |  |
| `round13-r13-048-unprintable-6054.smt2` | timeout | sat |  |
| `round13-r13-072-fuzz-string13.smt2` | timeout | sat |  |
| `round13-r13-076-fuzz-string7.smt2` | timeout | sat |  |
| `round14-r14-001-multiply-2415.smt2` | timeout | unsat |  |
| `round14-r14-001-translate-2415.smt2` | timeout | unsat |  |
| `round14-r14-001-unprintable-2415.smt2` | timeout | unsat |  |
| `round14-r14-011-multiply-2912.smt2` | sat | timeout |  |
| `round14-r14-024-fuzz-3889.smt2` | unsat | timeout |  |
| `round14-r14-029-multiply-3999.smt2` | timeout | sat |  |
| `round14-r14-034-multiply-4010.smt2` | sat | timeout |  |
| `round14-r14-041-fuzz-4033.smt2` | unknown | sat |  |
| `round14-r14-041-multiply-4033.smt2` | unknown | sat |  |
| `round14-r14-041-translate-4033.smt2` | unknown | sat |  |
| `round14-r14-041-unprintable-4033.smt2` | unknown | sat |  |
| `round14-r14-048-multiply-6054.smt2` | timeout | sat |  |
| `round14-r14-048-translate-6054.smt2` | timeout | sat |  |
| `round14-r14-048-unprintable-6054.smt2` | timeout | sat |  |
| `round14-r14-066-fuzz-string-concat.smt2` | unsat | timeout |  |
| `round14-r14-068-fuzz-string-ops.smt2` | unsat | timeout |  |
| `round14-r14-068-multiply-string-ops.smt2` | unsat | timeout |  |
| `round14-r14-072-fuzz-string13.smt2` | timeout | sat |  |
| `round14-r14-074-multiply-string3.smt2` | unsat | timeout |  |
| `round15-r15-001-multiply-2415.smt2` | timeout | unsat |  |
| `round15-r15-001-translate-2415.smt2` | timeout | unsat |  |
| `round15-r15-001-unprintable-2415.smt2` | timeout | unsat |  |
| `round15-r15-041-fuzz-4033.smt2` | unknown | sat |  |
| `round15-r15-041-multiply-4033.smt2` | unknown | sat |  |
| `round15-r15-041-translate-4033.smt2` | unknown | sat |  |
| `round15-r15-041-unprintable-4033.smt2` | unknown | sat |  |
| `round15-r15-048-multiply-6054.smt2` | timeout | sat |  |
| `round15-r15-048-unprintable-6054.smt2` | timeout | sat |  |
| `round15-r15-054-fuzz-issue-1566.smt2` | timeout | sat |  |
| `round16-r16-001-fuzz-2415.smt2` | timeout | sat |  |
| `round16-r16-001-multiply-2415.smt2` | timeout | unsat |  |
| `round16-r16-001-translate-2415.smt2` | timeout | unsat |  |
| `round16-r16-001-unprintable-2415.smt2` | timeout | unsat |  |
| `round16-r16-016-fuzz-3105.smt2` | timeout | sat |  |
| `round16-r16-029-unprintable-3999.smt2` | timeout | sat |  |
| `round16-r16-041-fuzz-4033.smt2` | unknown | sat |  |
| `round16-r16-041-multiply-4033.smt2` | unknown | sat |  |
| `round16-r16-041-translate-4033.smt2` | unknown | sat |  |
| `round16-r16-041-unprintable-4033.smt2` | unknown | sat |  |
| `round16-r16-048-multiply-6054.smt2` | timeout | sat |  |
| `round16-r16-048-unprintable-6054.smt2` | timeout | sat |  |
| `round17-r17-001-fuzz-2415.smt2` | timeout | sat |  |
| `round17-r17-001-multiply-2415.smt2` | timeout | unsat |  |
| `round17-r17-001-translate-2415.smt2` | timeout | unsat |  |
| `round17-r17-001-unprintable-2415.smt2` | timeout | unsat |  |
| `round17-r17-041-fuzz-4033.smt2` | unknown | sat |  |
| `round17-r17-041-multiply-4033.smt2` | unknown | sat |  |
| `round17-r17-041-translate-4033.smt2` | unknown | sat |  |
| `round17-r17-041-unprintable-4033.smt2` | unknown | sat |  |
| `round17-r17-048-multiply-6054.smt2` | timeout | sat |  |
| `round17-r17-048-unprintable-6054.smt2` | timeout | sat |  |
| `round17-r17-054-fuzz-issue-1566.smt2` | timeout | sat |  |
| `round18-r18-001-multiply-2415.smt2` | timeout | unsat |  |
| `round18-r18-001-translate-2415.smt2` | timeout | unsat |  |
| `round18-r18-001-unprintable-2415.smt2` | timeout | unsat |  |
| `round18-r18-037-multiply-4018.smt2` | timeout | sat |  |
| `round18-r18-041-fuzz-4033.smt2` | unknown | sat |  |
| `round18-r18-041-multiply-4033.smt2` | unknown | sat |  |
| `round18-r18-041-translate-4033.smt2` | unknown | sat |  |
| `round18-r18-041-unprintable-4033.smt2` | unknown | sat |  |
| `round18-r18-048-multiply-6054.smt2` | timeout | sat |  |
| `round18-r18-048-unprintable-6054.smt2` | timeout | sat |  |
| `round18-r18-054-fuzz-issue-1566.smt2` | timeout | sat |  |
| `round18-r18-076-fuzz-string7.smt2` | timeout | sat |  |
| `round19-r19-001-multiply-2415.smt2` | timeout | unsat |  |
| `round19-r19-001-translate-2415.smt2` | timeout | unsat |  |
| `round19-r19-001-unprintable-2415.smt2` | timeout | unsat |  |
| `round19-r19-016-fuzz-3105.smt2` | timeout | sat |  |
| `round19-r19-029-multiply-3999.smt2` | timeout | sat |  |
| `round19-r19-029-unprintable-3999.smt2` | timeout | sat |  |
| `round19-r19-041-fuzz-4033.smt2` | unknown | sat |  |
| `round19-r19-041-multiply-4033.smt2` | unknown | sat |  |
| `round19-r19-041-translate-4033.smt2` | unknown | sat |  |
| `round19-r19-041-unprintable-4033.smt2` | unknown | sat |  |
| `round19-r19-048-multiply-6054.smt2` | timeout | sat |  |
| `round19-r19-048-translate-6054.smt2` | timeout | sat |  |
| `round19-r19-048-unprintable-6054.smt2` | timeout | sat |  |
| `round19-r19-054-fuzz-issue-1566.smt2` | timeout | sat |  |
| `round19-r19-076-fuzz-string7.smt2` | timeout | sat |  |
| `round20-r20-001-fuzz-2415.smt2` | timeout | sat |  |
| `round20-r20-001-multiply-2415.smt2` | timeout | unsat |  |
| `round20-r20-001-translate-2415.smt2` | timeout | unsat |  |
| `round20-r20-001-unprintable-2415.smt2` | timeout | unsat |  |
| `round20-r20-016-fuzz-3105.smt2` | timeout | sat |  |
| `round20-r20-029-unprintable-3999.smt2` | timeout | sat |  |
| `round20-r20-041-fuzz-4033.smt2` | unknown | sat |  |
| `round20-r20-041-multiply-4033.smt2` | unknown | sat |  |
| `round20-r20-041-translate-4033.smt2` | unknown | sat |  |
| `round20-r20-041-unprintable-4033.smt2` | unknown | sat |  |
| `round20-r20-048-multiply-6054.smt2` | timeout | sat |  |
| `round20-r20-048-translate-6054.smt2` | timeout | sat |  |
| `round20-r20-048-unprintable-6054.smt2` | timeout | sat |  |
| `round20-r20-054-fuzz-issue-1566.smt2` | timeout | sat |  |
| `round20-r20-076-fuzz-string7.smt2` | timeout | sat |  |
| `round21-r21-001-multiply-2415.smt2` | timeout | unsat |  |
| `round21-r21-001-translate-2415.smt2` | timeout | unsat |  |
| `round21-r21-001-unprintable-2415.smt2` | timeout | unsat |  |
| `round21-r21-016-fuzz-3105.smt2` | timeout | sat |  |
| `round21-r21-029-unprintable-3999.smt2` | timeout | sat |  |
| `round21-r21-041-fuzz-4033.smt2` | unknown | sat |  |
| `round21-r21-041-multiply-4033.smt2` | unknown | sat |  |
| `round21-r21-041-translate-4033.smt2` | unknown | sat |  |
| `round21-r21-041-unprintable-4033.smt2` | unknown | sat |  |
| `round21-r21-048-multiply-6054.smt2` | timeout | sat |  |
| `round21-r21-048-translate-6054.smt2` | timeout | sat |  |
| `round21-r21-048-unprintable-6054.smt2` | timeout | sat |  |
| `round21-r21-054-fuzz-issue-1566.smt2` | timeout | sat |  |
| `round21-r21-072-fuzz-string13.smt2` | timeout | sat |  |
| `round21-r21-076-fuzz-string7.smt2` | timeout | sat |  |
| `round22-r22-001-fuzz-2415.smt2` | timeout | unsat |  |
| `round22-r22-001-multiply-2415.smt2` | timeout | unsat |  |
| `round22-r22-001-translate-2415.smt2` | timeout | unsat |  |
| `round22-r22-001-unprintable-2415.smt2` | timeout | unsat |  |
| `round22-r22-016-fuzz-3105.smt2` | timeout | sat |  |
| `round22-r22-041-fuzz-4033.smt2` | unknown | sat |  |
| `round22-r22-041-multiply-4033.smt2` | unknown | sat |  |
| `round22-r22-041-translate-4033.smt2` | unknown | sat |  |
| `round22-r22-041-unprintable-4033.smt2` | unknown | sat |  |
| `round22-r22-048-multiply-6054.smt2` | timeout | sat |  |
| `round22-r22-048-unprintable-6054.smt2` | timeout | sat |  |
| `round22-r22-072-fuzz-string13.smt2` | timeout | sat |  |
| `round22-r22-076-fuzz-string7.smt2` | timeout | sat |  |
| `round23-r23-001-fuzz-2415.smt2` | timeout | sat |  |
| `round23-r23-001-multiply-2415.smt2` | timeout | unsat |  |
| `round23-r23-001-translate-2415.smt2` | timeout | unsat |  |
| `round23-r23-001-unprintable-2415.smt2` | timeout | unsat |  |
| `round23-r23-016-fuzz-3105.smt2` | unknown | sat |  |
| `round23-r23-029-unprintable-3999.smt2` | unknown | sat |  |
| `round23-r23-037-multiply-4018.smt2` | timeout | sat |  |
| `round23-r23-041-fuzz-4033.smt2` | unknown | sat |  |
| `round23-r23-041-multiply-4033.smt2` | unknown | sat |  |
| `round23-r23-041-translate-4033.smt2` | unknown | sat |  |
| `round23-r23-041-unprintable-4033.smt2` | unknown | sat |  |
| `round23-r23-048-fuzz-6054.smt2` | timeout | sat |  |
| `round23-r23-048-multiply-6054.smt2` | timeout | sat |  |
| `round23-r23-048-unprintable-6054.smt2` | timeout | sat |  |
| `round23-r23-054-fuzz-issue-1566.smt2` | timeout | sat |  |
| `round24-r24-001-multiply-2415.smt2` | timeout | unsat |  |
| `round24-r24-001-translate-2415.smt2` | timeout | unsat |  |
| `round24-r24-001-unprintable-2415.smt2` | timeout | unsat |  |
| `round24-r24-029-multiply-3999.smt2` | timeout | sat |  |
| `round24-r24-029-unprintable-3999.smt2` | timeout | sat |  |
| `round24-r24-041-fuzz-4033.smt2` | unknown | sat |  |
| `round24-r24-041-multiply-4033.smt2` | unknown | sat |  |
| `round24-r24-041-translate-4033.smt2` | unknown | sat |  |
| `round24-r24-041-unprintable-4033.smt2` | unknown | sat |  |
| `round24-r24-048-multiply-6054.smt2` | timeout | sat |  |
| `round24-r24-048-translate-6054.smt2` | timeout | sat |  |
| `round24-r24-048-unprintable-6054.smt2` | timeout | sat |  |
| `round24-r24-076-fuzz-string7.smt2` | timeout | sat |  |
| `round25-r25-001-multiply-2415.smt2` | timeout | unsat |  |
| `round25-r25-001-translate-2415.smt2` | timeout | unsat |  |
| `round25-r25-001-unprintable-2415.smt2` | timeout | unsat |  |
| `round25-r25-016-fuzz-3105.smt2` | timeout | sat |  |
| `round25-r25-041-fuzz-4033.smt2` | unknown | sat |  |
| `round25-r25-041-multiply-4033.smt2` | unknown | sat |  |
| `round25-r25-041-translate-4033.smt2` | unknown | sat |  |
| `round25-r25-041-unprintable-4033.smt2` | unknown | sat |  |
| `round25-r25-048-multiply-6054.smt2` | timeout | sat |  |
| `round25-r25-048-unprintable-6054.smt2` | timeout | sat |  |
| `round25-r25-054-fuzz-issue-1566.smt2` | timeout | unsat |  |
| `round34-r34-001-multiply-2415.smt2` | timeout | unsat |  |
| `round34-r34-001-translate-2415.smt2` | timeout | unsat |  |
| `round34-r34-001-unprintable-2415.smt2` | timeout | unsat |  |
| `round34-r34-029-multiply-3999.smt2` | timeout | sat |  |
| `round34-r34-041-fuzz-4033.smt2` | unknown | sat |  |
| `round34-r34-041-multiply-4033.smt2` | unknown | sat |  |
| `round34-r34-041-translate-4033.smt2` | unknown | sat |  |
| `round34-r34-041-unprintable-4033.smt2` | unknown | sat |  |
| `round34-r34-048-fuzz-6054.smt2` | timeout | sat |  |
| `round34-r34-048-multiply-6054.smt2` | timeout | sat |  |
| `round34-r34-048-unprintable-6054.smt2` | timeout | sat |  |
| `round34-r34-076-fuzz-string7.smt2` | timeout | sat |  |
| `round37-r37-001-multiply-2415.smt2` | timeout | unsat |  |
| `round37-r37-001-translate-2415.smt2` | timeout | unsat |  |
| `round37-r37-001-unprintable-2415.smt2` | timeout | unsat |  |
| `round37-r37-041-fuzz-4033.smt2` | unknown | sat |  |
| `round37-r37-041-multiply-4033.smt2` | unknown | sat |  |
| `round37-r37-041-translate-4033.smt2` | unknown | sat |  |
| `round37-r37-041-unprintable-4033.smt2` | unknown | sat |  |
| `round37-r37-048-fuzz-6054.smt2` | timeout | sat |  |
| `round37-r37-048-multiply-6054.smt2` | timeout | sat |  |
| `round37-r37-048-unprintable-6054.smt2` | timeout | sat |  |
| `round37-r37-054-fuzz-issue-1566.smt2` | timeout | sat |  |
| `round37-r37-076-fuzz-string7.smt2` | timeout | sat |  |
| `z3ast-r33-z3ast-33-330003.smt2` | unknown | unknown |  |
| `z3ast-r33-z3ast-33-330005.smt2` | unknown | unknown |  |
| `z3ast-r33-z3ast-33-330015.smt2` | unknown | unknown |  |
| `z3ast-r33-z3ast-33-330024.smt2` | unknown | unknown |  |
| `z3ast-r33-z3ast-33-330046.smt2` | unknown | unknown |  |
| `z3ast-r33-z3ast-33-330083.smt2` | unknown | unknown |  |
| `z3ast-r33-z3ast-33-330084.smt2` | unknown | unknown |  |
| `z3ast-r33-z3ast-33-330085.smt2` | unknown | unknown |  |
| `z3ast-r33-z3ast-33-330136.smt2` | unknown | unknown |  |
| `z3ast-r33-z3ast-33-330150.smt2` | unknown | unknown |  |
| `z3ast-r33-z3ast-33-330154.smt2` | unknown | unknown |  |
| `z3ast-r33-z3ast-33-330168.smt2` | unknown | unknown |  |
| `z3ast-r33-z3ast-33-330197.smt2` | unknown | unknown |  |
| `z3ast-r33-z3ast-33-330225.smt2` | unknown | unknown |  |
| `z3ast-r33-z3ast-33-330230.smt2` | unknown | unknown |  |
| `z3ast-r33-z3ast-33-330237.smt2` | unknown | unknown |  |
| `z3ast-r33-z3ast-33-330297.smt2` | unknown | unknown |  |
| `z3ast-r33-z3ast-33-330304.smt2` | unknown | unknown |  |
| `z3ast-r33-z3ast-33-330321.smt2` | unknown | unknown |  |
| `z3ast-r33-z3ast-33-330328.smt2` | unknown | unknown |  |
| `z3ast-r33-z3ast-33-330374.smt2` | unknown | unknown |  |
| `z3ast-r36-z3ast-36-360011.smt2` | unknown | unknown |  |
| `z3ast-r36-z3ast-36-360028.smt2` | unknown | unknown |  |
| `z3ast-r36-z3ast-36-360077.smt2` | unknown | unknown |  |
| `z3ast-r36-z3ast-36-360158.smt2` | unknown | unknown |  |
| `z3ast-r36-z3ast-36-360201.smt2` | unknown | unknown |  |
| `z3ast-r36-z3ast-36-360264.smt2` | unknown | unknown |  |
| `z3ast-r36-z3ast-36-360268.smt2` | unknown | unknown |  |
| `z3ast-r36-z3ast-36-360288.smt2` | unknown | unknown |  |
| `z3ast-r36-z3ast-36-360299.smt2` | unknown | unknown |  |
| `z3ast-r36-z3ast-36-360328.smt2` | unknown | unknown |  |
| `z3ast-r36-z3ast-36-360332.smt2` | unknown | unknown |  |
| `z3ast-r36-z3ast-36-360394.smt2` | unknown | unknown |  |

**Retained inputs:** 419
**SAT/UNSAT disagreements:** 1
