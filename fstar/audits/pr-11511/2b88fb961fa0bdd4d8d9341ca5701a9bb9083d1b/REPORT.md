# F* audit: PR 11511 @ 2b88fb961fa0bdd4d8d9341ca5701a9bb9083d1b (base dd4179a5)

PR open at that SHA; no prior `fstar-nfv-audit:2b88fb961fa0bdd4d8d9341ca5701a9bb9083d1b` comment.

## Scope (partial)
Changed function selected: `bounded_filter_cfg::bounded` in `src/ast/rewriter/finite_set_rewriter.cpp` (patch lines 123-192), with its helpers `find_value` (38-65) and `is_extremum` (86-121). Source read via GitHub PR files API (patch hunk; head snapshot in /tmp/gh-aw/agent/snap/rw.patch). Base var_subst/rewriter behaviour read from trusted checkout.

Obligations (semantic, finite sets modeled as `list int`; filter(P,S)=S means forall, filter(P,S)=empty means not exists):
1. PROVED: fixed point (`find_value`, including the matching `<=`/`>=` bound pair giving x==b): forall x in S. (x=t /\ r x) <=> S=empty \/ (S={t} /\ r t); exists x in S. (x=t /\ r x) <=> t in S /\ r t (negated by rewrite). Lemmas ob1_*.
2. PROVED: `is_extremum`: a nonempty finite set has an element with maximal / minimal projection (has_max/has_min), and an empty set has none, so exists-filter = empty iff domain empty. Modeled over Int; Real is also totally ordered but not separately modeled.
3. PROVED: independent-guard rewrites (`!uses_bound_var`): forall x in S. d \/ r x <=> d \/ forall r; exists x in S. d /\ r x <=> d /\ exists r; implication guard as (not g) \/ c; constant body case (S=empty \/ c, S<>empty /\ c). Lemmas ob3_*.

No counterexample found; no reachable witness constructed.

## Correspondence and assumptions
F* quantifiers over a list model the finite-set filter semantics. Inherited: F* standard library, pinned Z3 4.13.3 backend. Assumed (manually reviewed, not mechanized): the C++ guard `uses_bound_var` correctly detects bound-variable independence; `inv_var_shifter`/`var_subst` de Bruijn handling is capture-safe (base `var_subst` uses `expr_safe_replace` when quantifiers are present, which shifts binders; reviewed, no defect observed); sort checks `b->get_sort()==target->get_sort()`; the early hook in th_rewriter. Note find_value requires `b` not to use bound var 0 only; outer-variable occurrences are lowered by remove_binder.

## Exclusions
Not covered: single-constructor single-field datatype fixed point (find_point lines 72-83), is_extremum's syntactic matching (subst(a,candidate)==b, structural), `reduce_app` normalization hook (194-204), mk_eq_bounded (208-229) and the mk_eq_core hook, th_rewriter.cpp changes, proof production (BR_REWRITE_FULL), removal of finite_set_simplifier/tactic files and their registrations, tests, C++ execution, memory safety, termination of repeated BR_REWRITE_FULL.

## Reproduce
See verification log (commands in cmd.txt); from the audit directory with fresh cache/out dirs.
