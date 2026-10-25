# F* audit: PR #11322 (head 9e53f4bc0214c14a3b11b892894712b148e2fdec, base 9fbc6e694b18c2f35cbfe53573892e9e8cd2f66f)

## Scope (partial)
Audited 1 changed function: `theory_array_full::assert_lambda_congruence()` (new, src/smt/theory_array_full.cpp, patch lines ~1024-1056 at head) and its call site in `assert_delayed_axioms()`.
Head source sha256 (decoded contents API) 8b185975c27f66f851848fbf9803836411ccdbacf9ea765cb0751a4e9add027f; base 578b1dc8efca6910b53982df288f0d13c01658f0183c8e6d00a19fd944be7a59.
**Excluded:** `theory_array_full.h` declaration (plumbing); `src/test/smt_context.cpp` regression tests (not executed, not modeled); `merge_eh` (unchanged); `assert_congruent`/`assert_congruent_core` internals (base code, assumed); the quantifier instantiation/e-matching that consumes the axiom; `has_non_beta_as_array` giveup logic; completeness of the traversal.

## Property and assumptions
Intended property (soundness of the fix): every axiom the new loop queues, n1 = n2 => forall k. select(n1,k) = select(n2,k), is valid in array semantics, and it suffices to refute the issue #11267 formula store(lambda x.x,7,0) = store(const 3,7,0).
Assumptions: arrays denote total functions with extensional equality (F* `int -> int`, with propositional equality of functions given by F* functional extensionality); `assert_congruent` queues exactly the axiom above (reviewed by reading theory_array_base.cpp::assert_congruent_core in the base checkout, equal at head per the diff not touching it); the E-graph ring `get_next()` enumerates the class of `root`.

## Obligations
1. O1 `o1_congruence_valid`, `o1b_store_congruence`: congruence axiom is valid for any pair, including stores over lambdas. **proved**.
2. O2 `o2_issue_instance_contradiction`, `o2_equality_unsat`: the issue formula, instantiated at k=8, yields 8=3, so the equality is unsatisfiable; the PR-queued axiom is sufficient to refute it. **proved**. No counterexample to soundness was found (the attempted refutation of O1 is impossible since the axiom is valid).
3. O3 `o3_sat_case_consistent`: for the PR's satisfiable regression (lambda x. ite(x=7,1,3)), all axiom instances hold, so the fix does not force spurious unsat there. **proved** (model-level only).

## Correspondence and manual review (not mechanized)
F* `store`/`const_arr`/lambda model the SMT array semantics, not Z3's E-graph. Manual observations on the C++: the worklist starts from m_lambdas, canonicalizes to roots, dedupes via `visited`; parents are pushed only when relevant and either a store whose base is in the root class or any map, so growth is bounded by finite parent lists; `assert_congruent` has fingerprint dedupe (so repeated final checks do not requeue), swaps operands by id so reversed operands are the same axiom; it returns early under `m_array_fake_support`. `r = FC_CONTINUE` only if `can_propagate()` (queued work), so no infinite loop absent new axioms. Termination across rounds, e-matching instantiation, and interaction with has_non_beta_as_array giveup are not proved. Worst-case cost is quadratic in class size per final check (all members paired with root only, so linear per class). Not proved: execution of C++, memory safety, completeness.

## Reproduce
`cd /tmp/gh-aw/agent/fstar-audit && mkdir cache out && /tmp/gh-aw/fstar/bin/fstar.exe --smt /tmp/gh-aw/fstar/lib/fstar/z3-4.13.3/bin/z3 --z3version 4.13.3 --include fstar --z3rlimit 10 --cache_dir cache --odir out Z3Pr11322LambdaCongruence.fst` (run from the repo's trusted base with --include pointing at fstar/).

## Verdict
proved for the three semantic obligations; scope partial as stated above.
