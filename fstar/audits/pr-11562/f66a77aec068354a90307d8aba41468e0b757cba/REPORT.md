# F* audit PR 11562 @ f66a77ae
Base 5bab8997. Source: src/smt/smt_internalizer.cpp (diff hunks ~lines 400-720; internalize_formula, internalize_quantifier, internalize_quantifier_polarity).

## Obligations (all proved)
1. Negation flips polarity as an involution; the possible-occurrence sets swap (internalize_formula Not case passes ~polarity).
2. Coverage: every possible occurrence polarity of a quantifier is handled: negative-possible => negative (Skolem/NNF) clause added; l_undef => both.
3. Clause literal arithmetic: premise=literal(q, !positive); clause ~premise \/ result equals source -> result.

## Correspondence
lbool -> LTrue/LFalse/LUndef; literal(var,sign) -> lit; do_pos/do_neg mirror the conditions polarity==l_undef and polarity!=l_true.

## Assumptions
NNF output (`nnf`) is equivalent to its source (not re-proved here; prior audit at 766f6d4 covered an abstract NNF). Callers pass correct polarity: callers using l_undef are conservative; l_true passed only for assertions/OR/AND/ite-branch roots under assert_default.

## Not covered (manual review)
The ite-branch l_true in internalize_deep (OP_ITE then/else under mk_root_clause) not proved; scoped-trail push/pop (m_quantifier_positive/negative, on_scope_exit rollback); proof-term construction; memory safety; enode creation for quantifier terms; other files (theory_*, tests, mechanical parameter changes) excluded.

## Reproduce
fstar.exe --smt z3 --z3version 4.13.3 --include fstar --z3rlimit 10 --cache_dir cache --odir out QuantPolarityInternalize.fst
F* 2026.09.27, Z3 4.13.3 (pinned).