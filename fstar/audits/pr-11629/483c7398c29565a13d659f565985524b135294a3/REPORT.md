# F* audit, PR 11629, head 483c7398c29565a13d659f565985524b135294a3 (base d6c9b4fbb31cb76e35cc325dd7e64b7c26c7d70f)

Partial scope; verdict inconclusive. Changed functions in fstar/Z3SortedProof.fst (this is itself an F* proof-checker module, not C++), read via the contents/patch API:
1. `integer_product_clause_equality` / `integer_clause_equality_witness`
2. `real_product_clause_equality` / `real_clause_equality_witness`
3. `product_equality_clause_facts` (complements of all literals other than the selected equality e).

Obligations:
- O1 (abstract soundness of clause replay): if e is a clause literal, facts hold, and the equality check is sound under facts plus the negations of the other literals, then the clause is true. PROVED in PRClauseEqualityModel.fst (clause_equality_sound).
- O2 (the filter removes only literals equal to e; duplicates of e are harmless): PROVED (filter_excludes_only_e).
- O3 (budget guard: facts<=29 and facts+lits<=30 imply the combined list is at most 30): PROVED (budget_bound).
- O4 (the real/integer equality checkers RP.equality_check and integer_product_equality are sound for the selected e): NOT re-verified; inconclusive. The PR's own lemmas (lemma_integer_product_clause_equality, lemma_real_product_clause_equality) were read but PR modules were not imported or built, per policy.

Correspondence/assumptions: the F* model abstracts literals as ints and the equality checker as a hypothesis (soundness of the existing checker under the complement facts). This hypothesis is the disputed part and is not discharged here. No counterexample was sought successfully; none was found by inspection. The patch's scoping guard D.scoped_args on the complements and the budget checks were read but not modelled.

Excluded: Z3CherryTests.fst, Z3SortedRealDocumentTests.fst, Z3SortedRootDocumentTests.fst, tools/test_native_bridge.ml, the earlier audit artifacts under fstar/audits/pr-11629/ff63fdc..., the modified lemma_integer_product_clause / real_product_clause dispatch, and all C++ (none changed). Nothing here is mechanized verification of the PR's modules, OCaml bridge, or solver.

Reproduce: cd to a work dir, run `timeout 120 /tmp/gh-aw/fstar/bin/fstar.exe --smt /tmp/gh-aw/fstar/lib/fstar/z3-4.13.3/bin/z3 --z3version 4.13.3 --z3rlimit 10 --cache_dir cache --odir out PRClauseEqualityModel.fst`. Inherited assumptions: F* standard library (FStar.List.Tot, FStar.Classical).