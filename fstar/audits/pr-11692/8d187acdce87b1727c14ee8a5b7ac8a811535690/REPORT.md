# F* audit: PR 11692 (`fstar-nfv-audit:8d187acdce87b1727c14ee8a5b7ac8a811535690`)

Head 8d187acdce87b1727c14ee8a5b7ac8a811535690, base 708879ef23599153d4f0adb3af58fb514e2c8942.
Source: `src/smt/smt_model_checker.cpp` (head sha256 a5105a3b..., base e2b83d02...), added lines 40-88 (`partial_arith_guard_cfg`) and 241-248 (`assert_neg_q_m`).

## Scope (partial)
One changed function group audited: `partial_arith_guard_cfg::reduce_app` plus its use in `model_checker::assert_neg_q_m`. Three obligations.
Excluded: `src/test/smt_context.cpp` (tests), `has_interp_at_zero`/`interp_at_zero` (only a gating predicate), real division/mod/rem sort handling (modelled only via integer div; the guard code is uniform over the four operators), `rewriter_tpl` traversal/memory/AST plumbing, var_subst, the evaluator, and all C++ execution semantics. The empirical corpus claims in the PR description are not checked.

## Property and assumptions
Intended: with the Skolem constants symbolic, the evaluated quantifier body must agree with the current model at a zero divisor, for any value the aux context could otherwise choose for the unevaluated `(div t s)`.
Assumptions: (A1) the evaluator leaves div/mod/rem with non-numeral divisors unevaluated (base `model_evaluator.cpp`/`arith_util::is_considered_partially_interpreted`, matching the PR text); evaluating them as free function `c` models the aux solver's freedom. (A2) `fi->get_interp()` instantiated with args equals the model's d0 (`D0`). (A3) Euclidean division at nonzero divisors is identical in both semantics (shared `ediv_nz`).

## Obligations (module `Z3MbqiDivGuard.fst`)
1. `base_diverges` (refutation of the unguarded base behaviour): witness `(div 0 x)` at x=0, d0=0, c=1 gives different values. PROVED. This reproduces the PR's motivation; it is not a counterexample to the PR.
2. `guard_sound`: for all d0, c, env and terms e, `sem_aux d0 c env (guard e) == sem_model d0 env e`. PROVED. This includes numeral divisors (skipped by the guard; the evaluator reduces them, including numeral 0 via d0 as in the model).
3. `guard_id`: terms without division are unchanged by the pass. PROVED.

No counterexample to the PR was found. Note one observation not modelled: `is_zero` is built with `mk_numeral(0, sort)`; for a divisor of Real or Int sort this is fine; others are unreachable for arith ops.

## Mapping and limits
`guard` models `reduce_app` bottom-up with BR_DONE (single visit, result not revisited); `Ite0`/`D0` model `m.mk_ite(is_zero, at_zero, f(args))`. Not mechanized: C++ execution, rewriter caching and soundness of `rewriter_tpl` with a custom cfg, free-variable handling in `var_subst` under quantifier bodies (de Bruijn indices), memory safety. The guard does not by itself establish MBQI completeness or termination.

## Reproduce
```
/tmp/gh-aw/fstar/bin/fstar.exe --smt /tmp/gh-aw/fstar/lib/fstar/z3-4.13.3/bin/z3 --z3version 4.13.3 --include fstar --z3rlimit 10 --cache_dir CACHE --odir OUT Z3MbqiDivGuard.fst
```
F* 2026.09.27; Z3 4.13.3 (pinned release backend). Exit code 0. No admit/assume/lax; only the F* standard library is inherited.
