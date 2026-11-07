# F* audit PR 11562 @ 8f52ea371d6674e3b5bfce7824b0654ff69180e2

Source: src/smt/smt_internalizer.cpp at head (sha256 of decoded content 5f3cbd45acca4e85a2c7e00689cd8dc84ee661069c35e0951c6ef60315feb3ad), internalize_formula L476-530, internalize_quantifier L655-676. Base 5bab89972dc48c2d5560b1e6e0df8297bd85e2ea.

## Obligations (all proved)
- O1: the negative-polarity NNF clause is added iff polarity may be negative (polarity != l_true); the positive clause iff l_undef.
- O2: NOT-gate recursion with ~polarity preserves occurrence polarity.
- O3: double negation restores polarity; l_undef over-approximates both polarities (used for gate children).
- Sanity check: top-level assert (l_true) under NOT yields l_false, so the negative clause only. This is a model check, not a counterexample.

## Mapping
lbool -> lbool; operator~ -> lneg; guards in internalize_quantifier -> adds_pos/adds_neg.

## Assumptions
Only F* core library semantics. Polarity arguments at call sites are assumed correct; the ~dozens of call-site polarity choices are not individually checked.

## Excluded / manually reviewed
Theory-file signature updates; internalize_quantifier_polarity (NNF call, defs internalization, proof construction, add_rel_watch, seen-set trail rollback); call-site polarity choices in internalize_deep (e.g. l_true for ITE then/else branches: manual review recommended); tests; the earlier audit of 766f6d4. Semantic model only; no C++ execution, memory safety, or solver-wide claims.

## Reproduce
F* 2026.09.27, z3 4.13.3:
/tmp/gh-aw/fstar/bin/fstar.exe --smt /tmp/gh-aw/fstar/lib/fstar/z3-4.13.3/bin/z3 --z3version 4.13.3 --z3rlimit 10 --cache_dir cache --odir out QuantPolarity.fst
