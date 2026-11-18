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
