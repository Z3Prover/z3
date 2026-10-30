# PR 11455 audit: finite-set size upper bound
Head 7664a1d6921c26f80ce76fe69ac24cd6fc01b3ac, base dad37c85122de03ec838d3d8528de1f341ead036.
Source: src/ast/rewriter/finite_set_axioms.cpp (head sha256 ab5b057de7d02e0d926063da06b4a1be6ea86e441eb528d28c109b85b686215d; base e0f2b540276d17e08c595375ae1c260a3a82548febe92a4469323480f5bfb9bd), function `finite_set_axioms::size_ub_axiom`, head lines 344-353 (new block).

## Behavior
New guard: `elem_sort->get_num_elements().is_finite()` (exact finite, excludes very-big and infinite) then adds unit `set.size(e) <= domain_size.size()`.
## Obligations (all proved in Z3FiniteSetSizeBound.fst)
1. O1 soundness: any set over an N-element domain has size <= N (proved).
2. O2 tightness: full set has size N, so bound is attained (proved).
3. O3 no over-restriction: prefix sets realise every size k in [0,N] (proved).
4. Motivating instance: FiniteSet Bool cannot have size 3 (proved).
No counterexample found. Guard correctly omits SS_FINITE_VERY_BIG (sizes >= 2^64, where uint64 is meaningless).
## Correspondence and assumptions
Element sort modeled as [0,N); set as membership predicate; size as count. Assumes `sort_size` of each element sort is exact when is_finite (checked by reading Bool=2, BV 1<<n for n<64, finite-set plugin 2^n for n<=30; datatype/dl/ff plugins not audited here). Rational conversion `rational(uint64_t)`, rewriter simplification, VERIFY on is_finite_set, add_unit plumbing and the C++ tests (src/test/finite_set.cpp) are manually reviewed only; not mechanized.
## Exclusions
Other axioms in size_ub_axiom (union, intersect, etc.), src/test/finite_set.cpp, and sort_size correctness of datatype/finite-field/datalog sorts.
## Reproduce
timeout 120 /tmp/gh-aw/fstar/bin/fstar.exe --smt /tmp/gh-aw/fstar/lib/fstar/z3-4.13.3/bin/z3 --z3version 4.13.3 --z3rlimit 10 --include fstar --cache_dir cache --odir out Z3FiniteSetSizeBound.fst
