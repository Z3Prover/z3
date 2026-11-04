# F* audit of PR #11531 @ 6c2ed83b (base 605d1d83)

## Changed functions audited (3 of 3 relevant)
1. demodulator_simplifier::mk_instance_proof (demodulator_simplifier.cpp; removed groundness checks on args/bindings). sha256 of head file: 5366e906471dec09357147d2b615b53ff59641a130db9caf29a479a58c4ab6db
2. demodulator_simplifier::rewrite1 (proof built before dependency recording; on failure `continue` to next demodulator).
3. demodulator_match_subst::match_args (m_subst.reset() hoisted; in proof mode the all-args-equal fast path now binds lhs vars to themselves). sha256: ef9e2e29226b7761007c69f3558e52034f5a9fe42071f347e6487a224d0645fe

Excluded: demodulator_rewriter.h doc/comment edits, src/test/simplifier.cpp regressions, the rewriter_def.h quantifier-congruence code that binds free vars in proofs (not in this diff), substitution::apply de Bruijn shifting under quantifiers in rhs (base code, reviewed by reading only).

## Obligations (all proved)
- O1 subst_eval: evaluating subst b t in outer env r equals evaluating t in env k->eval r (b k); non-ground bindings are sound.
- O2 instance_sound: if the universal equation l=rhs holds for every env, every (possibly non-ground) instance holds in every outer env, i.e. the PR_QUANT_INST step is semantically valid.
- O3 subst_id: identity bindings (exact-match fast path) give qe[s]==qe, so the syntactic equality shortcut in mk_instance_proof is justified.

## Correspondence
term/Var/App model de Bruijn exprs; subst models var_subst with bindings; binders inside terms are NOT modelled (the lemma is for binder-free instance bodies and the outer environment stands for enclosing quantifiers). Source guards: before the PR, non-ground args returned nullptr; now they are accepted, and a missing binding or missing proof still returns nullptr and rewrite1 skips (continue), which is the safe direction in proof mode.

## Assumptions and manual review
- var_subst/shifting is correct under binders in the rhs (not proved here).
- In proof mode with no match failure, get_binding for each variable succeeds; if not, mk_instance_proof returns nullptr and the rewrite is refused, so completeness gaps cannot cause unsound proofs.
- Observation (not a defect): in the fast path match_args_aux_proc throws no_match on quantifiers in lhs args, returning false; this only loses rewrites.
- Inherited: F* core library and Z3 4.13.3 backend.

## Reproduce
/tmp/gh-aw/fstar/bin/fstar.exe --smt /tmp/gh-aw/fstar/lib/fstar/z3-4.13.3/bin/z3 --z3version 4.13.3 --include /home/runner/work/z3/z3/fstar --z3rlimit 10 --cache_dir cache --odir out Z3DemodNonGround.fst


Versions:
F* 2026.09.27
platform=Linux_x86_64
system=Unix
compiler=OCaml 5.3.0
date=2026-09-27 16:52:08 +0000
commit=7deb38a27c86990664c6b41e4b6093597acdebd4
Z3 version 4.13.3 - 64 bit
