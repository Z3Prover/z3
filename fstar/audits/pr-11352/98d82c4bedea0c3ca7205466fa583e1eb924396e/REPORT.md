# F* audit, PR 11352 @ 98d82c4bedea0c3ca7205466fa583e1eb924396e (base 9dbe8c83fcadaba50a607236894f72a63959a5da)

**Partial scope.** Not a full-PR or C++ execution proof.

## Changed behavior
Adds `solver::assert_domain_selects` (src/sat/smt/array_axioms.cpp) and `theory_array_full::instantiate_domain_selects` (src/smt/theory_array_full.cpp). They are called from the default-map and default-store axioms. For small finite index domains (Bool, BV width <= 5, enum datatypes, total tuples <= 32) they instantiate `select(arr, i)` for every domain tuple, so the arbitrary epsilon index cannot hide a conflict at unstored indices. The two functions are textually identical modulo the API names.

## Obligations (all proved, F* DomainSelects.fst)
1. O1 `decode_inrange`: every k < total decodes (r % size; r /= size) to an in-range tuple. Proved.
2. O2 `encode_bound` + `roundtrip`: every in-range tuple is produced by some k < total, so enumeration is complete (covers the whole finite domain). Proved.
3. O3 `step_ok`, `bv_size_ok`: guard `total > 32 => return false` keeps each multiplication at most 32*32, so no unsigned overflow; BV sizes 1..5 give 2..32 values. Proved.

## Correspondence / assumptions
The F* model is a pure mixed-radix model of the loop indices (list of domain sizes). Assumed and not mechanized: the value vectors really have the claimed sizes and contain distinct domain elements (Bool true/false, numerals 0..2^n-1, enum constructors); `a.mk_select`/`e_internalize`/`ctx.internalize` behave as intended; the returned "new enode" flag guarantees termination of the propagation loop (manually read: `prop` is true only when a new select enode was created, so it is monotonically bounded). Only the base F* library/Prims are used; no base fstar/ modules are imported. Z3 backend is the pinned release, not built from the PR.

## Not covered (excluded)
Soundness of the overall array theory, the `has_large_domain` guard semantics, mark_as_relevant side effects, performance (up to 32 extra selects per store/map term, up to 3 arrays), the `prop |= ...` change in the store axiom, the `|| prop` return change, memory safety, AST plumbing, theory_array_full.h/array_solver.h declarations, and the regression tests. No refutation witness was constructed; the unsat example in the PR description was not run (PR code not executed).

## Reproduce
See verification_log. Versions: F* 2026.09.27, Z3 4.13.3.
