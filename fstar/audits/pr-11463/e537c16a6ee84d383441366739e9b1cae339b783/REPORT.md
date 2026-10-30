# F* audit of PR 11463 (head e537c16a6ee84d383441366739e9b1cae339b783, base 51160006282b714bfae25627dbcc608f9531e8fa)

Scope: one changed function, `theory_array_full::instantiate_lambda_defaults` (new), plus its call site in `assert_delayed_axioms` (src/smt/theory_array_full.cpp, lines ~1000-1060 at head). Removal of eager `instantiate_default_lambda_def_axiom` calls in `add_lambda` and `internalize_term_core` was reviewed only informally.

## Obligations
1. O1 (proved): a relevant lambda is skipped iff its root class is a singleton, it has at least one relevant parent, and every relevant parent is a non-array-family beta redex. Irrelevant lambdas are skipped.
2. O2 (proved): any relevant array-family or non-beta relevant parent prevents skipping.
3. O3 (proved): if the pass returns false, every non-skipped lambda was attempted (fingerprint recorded). Returning true yields FC_CONTINUE before giveup/done paths (O4, proved).

## Correspondence
`parent`/`lam` abstract enode flags: is_relevant, get_family_id()==get_id(), ctx.is_beta_redex, root class size==1. `scan` mirrors the parent loop incl. break. `instantiate` abstracts add_fingerprint + try_assign_eq (assign is arbitrary).

## Assumptions / not proved
- ctx.is_beta_redex(p,n) semantics are taken as an opaque boolean (base: theory_array_base::is_beta_redex; select checks arg0 root, map/store always true).
- No proof that skipping defaults is semantically sound for model construction/final check (that pointwise consumers do not observe the default); this is the PR's disputed claim and remains manually reviewed. Note the PR itself reports a timing-out satisfiable probe (nonconstant integer lambda alias).
- Not covered: C++ memory safety, trail/backtracking of fingerprints, try_assign_eq semantics, removed eager axioms, whether deferral can cause FC_DONE with missing defaults via other paths (has_non_beta_as_array excludes non-select/uninterp parents but not all cases).
- No counterexample was sought beyond the modeled guards; none established. Inherits only F* standard library (FStar.List.Tot) assumptions.

## Reproduce
See verification log. Fresh cache and out dirs.
