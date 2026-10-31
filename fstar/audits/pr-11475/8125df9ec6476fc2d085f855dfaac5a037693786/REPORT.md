# F* audit PR #11475 @ 8125df9ec6476fc2d085f855dfaac5a037693786 (base d687b6a18d03834ec2bfaa72647890c444748a09)

Partial scope: only `src/opt/opt_context.cpp` function `mod_div_purifier` (lines ~1287-1355 at head, sha256 of head file 242af2e7b7c6e242776a9a286e0e113165657c8494b34955bb496a61cc434e63; base file 560746fb...). This is a semantic audit of the purification step, not mechanized verification of C++.

## Obligations
1. O1 (proved): for k != 0, q=t/k, r=t%k satisfy t = k*q+r, 0<=r<|k| (the defs the purifier emits).
2. O2 (proved): those defs determine q and r uniquely (also negative k).
3. O3 (proved): exists-q,r (defs /\ B) <=> B[div,mod]; forall-q,r (defs => B) <=> B[div,mod]. This matches the exists (and) / forall (implies) encoding in `operator()`.
No counterexample was found for these obligations.

## Correspondence / assumptions
- F* `/` and `%` on int are Euclidean, as SMT-LIB div/mod (sanity checks incl. negative operands in T.fst, verified). Division by zero is excluded; the C++ guards k numeral and non-zero (`!k.is_zero()`, also enforced by linear_arith_fragment).
- Manually reviewed, not mechanized: instantiate/expr_abstract de Bruijn plumbing; nested quantifiers are purified first (replace() does not descend into quantifiers, so div/mod are bound by the innermost enclosing quantifier, which is correct since defs for t mention only the quantifier's own instantiated constants and outer free constants); caching and sharing of (t,k) pairs via the mod key for both div and mod.
- No assumptions beyond F* standard library (FStar.Math.Lemmas, FStar.Classical) and the pinned Z3 backend.

## Excluded changes (not audited)
- context::eliminate_quantifiers(expr_ref_vector&) (cache, budget, cancellation handling) and context::eliminate_quantifiers(expr*) (qe vs qe_rec agreement check, equivalence check via mk_smt_solver; soundness rests on the qe tactic results being checked equivalent and the SMT check returning unsat).
- linear_arith_fragment fragment recognition and eliminate_with.
- The m.inc() early return in normalize, the changes in optimize-related cancellation, opt_context.h, opt_params.hpp, CMake/test changes (src/test/opt_quantifiers.cpp).
- Equivalence of the qe outputs to the input (relies on the external check; not modeled).

## Reproduce
`cd /tmp/gh-aw/agent/fstar-audit && bash run.sh` (fresh cache each). F* 2026.09.27, Z3 4.13.3 independent backend.
