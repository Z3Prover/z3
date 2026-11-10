# VerCors C++ audit PR 11354 @ 50e9c308680cb14d0cbb8ec4670973ecbf090a42
Base 9dbe8c83fcadaba50a607236894f72a63959a5da. VerCors 2.4.0 (bundled Silicon/Z3, pinned release at /tmp/gh-aw/vercors).

## Selected function
`check_array_map_coherence` in `src/ast/rewriter/array_map_coherence.h` (new file, git blob d1d69e44, sha256 of decoded content f575315fbc967ac8d0f3598d2b299a84b1b3a933fb20eeaa94d74aa3cfee5cce). Selected region: domain-size loop, approx. lines 158-174 of head file (the `for (i < get_array_arity(s))` block computing `domain_size`, `exceeds`).

## Obligations (DomainSize.cpp, `domain_fits`)
1. No unsigned wraparound in `domain_size *= size` (asserted product <= n): VERIFIED on extract.
2. No division by zero in `n / size`: VERIFIED only under environment precondition sz[i] >= 1 (not established from source; Z3 sort_size of a finite sort could in principle be 0 - unchecked).
3. Result `*out >= 1` and `*out <= n || *out == 1`, memory-safe reads: VERIFIED on extract.
Non-vacuity: preconditions are satisfiable (e.g. arity 2, sz={2,3}, n=6); a calling witness unit could not be built (VerCors: "not possible to call this object" for C++ function calls), so non-vacuity is argued manually, not machine-checked.

## Outcome: INCONCLUSIVE
The extract verifies, but correspondence is not faithful: source uses uint64_t for domain_size and size.size() (n is size_t/unsigned from `indices.size()`), VerCors C++ frontend supports only 32-bit unsigned int here (`unsigned long`, `unsigned long long`, `uint64_t` rejected). Proof is therefore for a 32-bit model only. Per policy, width mismatch -> abstain from a conclusive verdict. No counterexample found.

## Abstractions
sort_size/get_array_domain/is_uninterp modeled as arrays sz/finite/uninterp read-only; `continue` on uninterpreted retained; short-circuit order retained; `break` retained.

## Exclusions
Other functions/obligations in the header (definition collection, `collect` lambda, store-index matching loop), src/sat/smt/array_axioms.cpp, array_solver.*, src/smt/theory_array_full.*, src/test/smt_context.cpp, and fstar audit files: not selected (templates, ASTs, obj_map, lambdas, RAII unsupported/conservatively excluded). Soundness of l_true/l_false returns and propagation not covered.

## Reproduce
Fetch file at head SHA, then in a clean directory: `/tmp/gh-aw/vercors/vercors --lang cpp --backend silicon --dev-total-timeout 60 $PWD/DomainSize.cpp` (exit 0, "Verification completed successfully.").
