# F* audit PR #11551 @ bddf23d57096bec3044c7795bf8737b2c744fb78 (base c79e8787949d31c3559371ba307f2dda2d2b3018)

Scope: partial. Changed functions selected (3): (1) smt2_printer concat branch in src/ast/ast_smt2_pp.cpp (n-ary concat printed as nested binary), (2) qsat.cpp qsat_qe `l_false` result re-quantification (loop over m_vars levels i=n-1..1, then m_free_vars), (3) the same file's level-parity use of is_exists.
Head sources fetched via contents API: src/qe/qsat.cpp sha256 d1507f58215e35fc7c960ed0d7af8c409061e7fa01feced9923802fe4a1e6b97 (lines ~1330-1356; is_exists at ~711; hoist at ~757), src/ast/ast_smt2_pp.cpp sha256 bbc21939d935bc74565a73e2e6ddbc1099f3c815acb0a721d0bd8981dc9155ae.

## Obligations (model-level, checked in Pr11551Audit.fst)
A. PROVED (model): left-nested binary concat of args equals positional n-ary concat value (concat3_left_eq_right, foldl_is_sem). Models concat as a*2^w+b over naturals.
B. PROVED (model): wrap_q uses is_exists(i)=i%2==0; level 1 maps to exists, levels alternate.
C. PROVED (model): descending loop i=n-1..1 yields prefix in order 1..n-1 (wrap_down_sorted).

## Not established
- Counterexample search: no witness found; no refutation claimed.
- Semantic soundness of the qsat re-quantification (that the wrapped formula is equivalent to the input quantifier-elimination result, that polarity of hoisted levels in m_vars matches input polarity, that vars in m_vars[i] occurring in m_answer are exactly the auxiliary projection variables, interaction with the later m_free_vars filtering) is NOT mechanized: obligations B and C only check parity arithmetic and loop order, not the QE semantics. Verdict therefore inconclusive.
- Dropped trailing-blank-line removal and the pp_fdecl_name bvsdiv/bvudiv/bvsrem/bvurem/bvsmod renaming (BV *_i ops printed as total SMT-LIB names: semantics differ for division by zero, since *_i are the unspecified-at-zero variants) and the flat_assoc concat guard: excluded, manually unreviewed. Tests (mbp_qel.cpp, smt2print_parse.cpp) excluded.
- C++ execution, memory safety, AST plumbing not verified.

## Assumptions
Only F* standard library (Prims, FStar.Math.Lemmas not required) and Z3 4.13.3 SMT backend. No admit/assume. No base modules imported.

## Reproduce
cd /tmp/gh-aw/agent/fstar-audit && timeout 120 /tmp/gh-aw/fstar/bin/fstar.exe --smt /tmp/gh-aw/fstar/lib/fstar/z3-4.13.3/bin/z3 --z3version 4.13.3 --include /home/runner/work/z3/z3/fstar --z3rlimit 10 --cache_dir cache --odir out Pr11551Audit.fst
