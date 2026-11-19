# c3mv String Fuzz Findings

## Scope

Differential fuzzing compared the `c3mv` branch against `master`, preserving
the c3mv default `nseq` string solver.

## Reproducible finding

`3911.smt2` and a minimized reproducer distinguish c3mv from master:

```smt2
(set-logic ALL)
(assert (str.in.re "" ((_ re.loop 189 0) (str.to.re ""))))
(check-sat)
```

- c3mv: `sat`
- master: `unsat`

The loop bounds are inverted (`lo=189`, `hi=0`) and should denote the empty
regular language.

## Reproducer

The minimized case is stored at:

- `string-fuzz/fix-re-loop-inverted-bounds.smt2`

## Status

This branch records the fuzz finding and regression input. It does not change
the c3mv `nseq` default or apply an implementation fix.

## Fix applied

The nseq membership path now rejects parameterized regex loops with
`low > high` as false, and the expression rewriter applies the same guard.
This keeps `smt.string_solver=nseq` and avoids changing the c3mv default.

Verified:

- `C:\z3test\regressions\smt2\3911.smt2`: c3mv `unsat`, master `unsat`
- `string-fuzz/fix-re-loop-inverted-bounds.smt2`: c3mv `unsat`, master `unsat`
- `test-z3 seq_rewriter`: PASS

## Continued fuzz rounds

### Broad Round 38

- Method: source-guided SMT2 mutation
- Fixed seed range: 380000-380499
- Generated: 500
- Timeout: 2 seconds
- Strict c3mv-underperformance retained: 0
- c3mv default: `nseq`
- Master oracle: `master`
- CSV: `string-fuzz-broad-38.csv`

### Broad Round 39

- Method: Z3 AST expression fuzzing
- Fixed seed range: 390000-390399
- Generated: 400
- Timeout: 2 seconds
- Strict c3mv-underperformance retained: 0
- c3mv default: `nseq`
- Master oracle: `master`
- CSV: `string-fuzz-z3ast-39.csv`

### Broad Round 40

- Method: supplemental StringFuzz transform round
- StringFuzz revision: `5507894ed5d94ed36098753357d33adee182b298`
- Modes: `fuzz`, `multiply`, `translate`, `unprintable`
- Generated: 208
- Timeout: 2 seconds
- Strict c3mv-underperformance retained: 0
- c3mv default: `nseq`
- Master oracle: `master`
- CSV: `string-fuzz-round-40.csv`

### Broad Round 41

- Method: source-guided SMT2 mutation
- Fixed seed range: 410000-410499
- Generated: 500
- Timeout: 2 seconds
- Strict c3mv-underperformance retained: 0
- c3mv default: `nseq`
- Master oracle: `master`
- CSV: `string-fuzz-broad-41.csv`

### Broad Round 42

- Method: Z3 AST expression fuzzing
- Fixed seed range: 420000-420399
- Generated: 400
- Timeout: 2 seconds
- Strict c3mv-underperformance retained: 0
- c3mv default: `nseq`
- Master oracle: `master`
- CSV: `string-fuzz-z3ast-42.csv`

### Broad Round 43

- Method: supplemental StringFuzz transform round
- StringFuzz revision: `5507894ed5d94ed36098753357d33adee182b298`
- Modes: `fuzz`, `multiply`, `translate`, `unprintable`
- Generated: 208
- Timeout: 2 seconds
- Strict c3mv-underperformance retained: 1
- c3mv default: `nseq`
- Master oracle: `master`
- CSV: `string-fuzz-round-43.csv`

### Broad Round 44

- Method: source-guided SMT2 mutation
- Fixed seed range: 440000-440499
- Generated: 500
- Timeout: 2 seconds
- Strict c3mv-underperformance retained: 0
- c3mv default: `nseq`
- Master oracle: `master`
- CSV: `string-fuzz-broad-44.csv`

### Broad Round 45

- Method: Z3 AST expression fuzzing
- Fixed seed range: 450000-450399
- Generated: 400
- Timeout: 2 seconds
- Strict c3mv-underperformance retained: 0
- c3mv default: `nseq`
- Master oracle: `master`
- CSV: `string-fuzz-z3ast-45.csv`

### Broad Round 46

- Method: supplemental StringFuzz transform round
- StringFuzz revision: `5507894ed5d94ed36098753357d33adee182b298`
- Modes: `fuzz`, `multiply`, `translate`, `unprintable`
- Generated: 208
- Timeout: 2 seconds
- Strict c3mv-underperformance retained: 1
- c3mv default: `nseq`
- Master oracle: `master`
- CSV: `string-fuzz-round-46.csv`

### Broad Round 47

- Method: source-guided SMT2 mutation
- Fixed seed range: 470000-470499
- Generated: 500
- Timeout: 2 seconds
- Strict c3mv-underperformance retained: 0
- c3mv default: `nseq`
- Master oracle: `master`
- CSV: `string-fuzz-broad-47.csv`

### Broad Round 48

- Method: Z3 AST expression fuzzing
- Fixed seed range: 480000-480399
- Generated: 400
- Timeout: 2 seconds
- Strict c3mv-underperformance retained: 0
- c3mv default: `nseq`
- Master oracle: `master`
- CSV: `string-fuzz-z3ast-48.csv`

### Broad Round 49

- Method: supplemental StringFuzz transform round
- StringFuzz revision: `5507894ed5d94ed36098753357d33adee182b298`
- Modes: `fuzz`, `multiply`, `translate`, `unprintable`
- Generated: 208
- Timeout: 2 seconds
- Strict c3mv-underperformance retained: 1
- c3mv default: `nseq`
- Master oracle: `master`
- CSV: `string-fuzz-round-49.csv`

### Broad Round 50

- Method: source-guided SMT2 mutation
- Fixed seed range: 500000-500499
- Generated: 500
- Timeout: 2 seconds
- Strict c3mv-underperformance retained: 0
- c3mv default: `nseq`
- Master oracle: `master`
- CSV: `string-fuzz-broad-50.csv`

### Broad Round 51

- Method: Z3 AST expression fuzzing
- Fixed seed range: 510000-510399
- Generated: 400
- Timeout: 2 seconds
- Strict c3mv-underperformance retained: 0
- c3mv default: `nseq`
- Master oracle: `master`
- CSV: `string-fuzz-z3ast-51.csv`

### Broad Round 52

- Method: supplemental StringFuzz transform round
- StringFuzz revision: `5507894ed5d94ed36098753357d33adee182b298`
- Modes: `fuzz`, `multiply`, `translate`, `unprintable`
- Generated: 208
- Timeout: 2 seconds
- Strict c3mv-underperformance retained: 0
- c3mv default: `nseq`
- Master oracle: `master`
- CSV: `string-fuzz-round-52.csv`

### Broad Round 53

- Method: source-guided SMT2 mutation
- Fixed seed range: 530000-530499
- Generated: 500
- Timeout: 2 seconds
- Strict c3mv-underperformance retained: 0
- c3mv default: `nseq`
- Master oracle: `master`
- CSV: `string-fuzz-broad-53.csv`

### Broad Round 54

- Method: Z3 AST expression fuzzing
- Fixed seed range: 540000-540399
- Generated: 400
- Timeout: 2 seconds
- Strict c3mv-underperformance retained: 0
- c3mv default: `nseq`
- Master oracle: `master`
- CSV: `string-fuzz-z3ast-54.csv`

### Broad Round 55

- Method: supplemental StringFuzz transform round
- StringFuzz revision: `5507894ed5d94ed36098753357d33adee182b298`
- Modes: `fuzz`, `multiply`, `translate`, `unprintable`
- Generated: 208
- Timeout: 2 seconds
- Strict c3mv-underperformance retained: 0
- c3mv default: `nseq`
- Master oracle: `master`
- CSV: `string-fuzz-round-55.csv`

### Broad Round 56

- Method: source-guided SMT2 mutation
- Fixed seed range: 560000-560499
- Generated: 500
- Timeout: 2 seconds
- Strict c3mv-underperformance retained: 0
- c3mv default: `nseq`
- Master oracle: `master`
- CSV: `string-fuzz-broad-56.csv`

### Broad Round 57

- Method: Z3 AST expression fuzzing
- Fixed seed range: 570000-570399
- Generated: 400
- Timeout: 2 seconds
- Strict c3mv-underperformance retained: 0
- c3mv default: `nseq`
- Master oracle: `master`
- CSV: `string-fuzz-z3ast-57.csv`

### Broad Round 58

- Method: supplemental StringFuzz transform round
- StringFuzz revision: `5507894ed5d94ed36098753357d33adee182b298`
- Modes: `fuzz`, `multiply`, `translate`, `unprintable`
- Generated: 208
- Timeout: 2 seconds
- Strict c3mv-underperformance retained: 0
- c3mv default: `nseq`
- Master oracle: `master`
- CSV: `string-fuzz-round-58.csv`

### Broad Round 59

- Method: source-guided SMT2 mutation
- Fixed seed range: 590000-590499
- Generated: 500
- Timeout: 2 seconds
- Strict c3mv-underperformance retained: 0
- c3mv default: `nseq`
- Master oracle: `master`
- CSV: `string-fuzz-broad-59.csv`

### Broad Round 60

- Method: Z3 AST expression fuzzing
- Fixed seed range: 600000-600399
- Generated: 400
- Timeout: 2 seconds
- Strict c3mv-underperformance retained: 0
- c3mv default: `nseq`
- Master oracle: `master`
- CSV: `string-fuzz-z3ast-60.csv`

### Broad Round 61

- Method: supplemental StringFuzz transform round
- StringFuzz revision: `5507894ed5d94ed36098753357d33adee182b298`
- Modes: `fuzz`, `multiply`, `translate`, `unprintable`
- Generated: 208
- Timeout: 2 seconds
- Strict c3mv-underperformance retained: 1
- c3mv default: `nseq`
- Master oracle: `master`
- CSV: `string-fuzz-round-61.csv`

### Broad Round 62

- Method: source-guided SMT2 mutation
- Fixed seed range: 620000-620499
- Generated: 500
- Timeout: 2 seconds
- Strict c3mv-underperformance retained: 0
- c3mv default: `nseq`
- Master oracle: `master`
- CSV: `string-fuzz-broad-62.csv`

### Broad Round 63

- Method: Z3 AST expression fuzzing
- Fixed seed range: 630000-630399
- Generated: 400
- Timeout: 2 seconds
- Strict c3mv-underperformance retained: 0
- c3mv default: `nseq`
- Master oracle: `master`
- CSV: `string-fuzz-z3ast-63.csv`

### Broad Round 64

- Method: supplemental StringFuzz transform round
- StringFuzz revision: `5507894ed5d94ed36098753357d33adee182b298`
- Modes: `fuzz`, `multiply`, `translate`, `unprintable`
- Generated: 208
- Timeout: 2 seconds
- Strict c3mv-underperformance retained: 1
- c3mv default: `nseq`
- Master oracle: `master`
- CSV: `string-fuzz-round-64.csv`

### Broad Round 65

- Method: source-guided SMT2 mutation
- Fixed seed range: 650000-650499
- Generated: 500
- Timeout: 2 seconds
- Strict c3mv-underperformance retained: 0
- c3mv default: `nseq`
- Master oracle: `master`
- CSV: `string-fuzz-broad-65.csv`

### Broad Round 66

- Method: Z3 AST expression fuzzing
- Fixed seed range: 660000-660399
- Generated: 400
- Timeout: 2 seconds
- Strict c3mv-underperformance retained: 0
- c3mv default: `nseq`
- Master oracle: `master`
- CSV: `string-fuzz-z3ast-66.csv`

### Broad Round 67

- Method: supplemental StringFuzz transform round
- StringFuzz revision: `5507894ed5d94ed36098753357d33adee182b298`
- Modes: `fuzz`, `multiply`, `translate`, `unprintable`
- Generated: 208
- Timeout: 2 seconds
- Strict c3mv-underperformance retained: 0
- c3mv default: `nseq`
- Master oracle: `master`
- CSV: `string-fuzz-round-67.csv`

### Broad Round 68

- Method: source-guided SMT2 mutation
- Fixed seed range: 680000-680499
- Generated: 500
- Timeout: 2 seconds
- Strict c3mv-underperformance retained: 0
- c3mv default: `nseq`
- Master oracle: `master`
- CSV: `string-fuzz-broad-68.csv`

### Broad Round 69

- Method: Z3 AST expression fuzzing
- Fixed seed range: 690000-690399
- Generated: 400
- Timeout: 2 seconds
- Strict c3mv-underperformance retained: 0
- c3mv default: `nseq`
- Master oracle: `master`
- CSV: `string-fuzz-z3ast-69.csv`

### Broad Round 70

- Method: supplemental StringFuzz transform round
- StringFuzz revision: `5507894ed5d94ed36098753357d33adee182b298`
- Modes: `fuzz`, `multiply`, `translate`, `unprintable`
- Generated: 208
- Timeout: 2 seconds
- Strict c3mv-underperformance retained: 1
- c3mv default: `nseq`
- Master oracle: `master`
- CSV: `string-fuzz-round-70.csv`
