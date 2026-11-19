## Scope
Head 55f02f22b7ef43b7e234a27ce7dc18412f38cee9, base 8573212ffea377844c322487224accff54809594. Head blob sha256: Z3SortedRealProduct.fst 779f2f7a...0de9 (214 lines), Z3SortedRealOrder.fst ff0370b3...c0 (194 lines), Z3SortedRootDocument.fst e6d05f7c...df (1151 lines). Fetched via contents API.

## Obligations
1. Z3SortedRealProduct.fst (lines ~150-165, lemma_multiply_positive / lemma_multiply_nonpositive): x>0,y>0 => x*y>0; opposite-sign weak bounds => x*y<=0. PROVED (FStar.Real).
2. Z3SortedRealOrder.fst lemma_subtract_zero (x-0==x). PROVED.
3. Z3SortedRootDocument.fst rule_shape (lines ~297-303): th-lemma label preserved, other unlisted payloads erased, idempotent. PROVED on a reduced rule type (Asserted/Unverified/Other), not the full Z3UnifiedProof.rule.

## Correspondence and assumptions
F* models mirror the real-valued arithmetic facts and the shape of rule_shape. Not mechanized: the full checker functions (positive_product, nonpositive_product, candidate search, budget), the PR modules type-checking, lemma_node_shape against SP.* predicates, OCaml/Python tests, and C++ execution. Assumes FStar.Real/Prims standard-library axioms; PR proof modules not imported as premises; no admit/assume.

## Excluded
Z3SortedProof.fst (+413), Z3SortedRealLinear.fst, Z3NnfReplay.fst change, all test files, tools/*, ocaml_runtime, prior audit files, remaining parts of the product checker (candidate/nested_candidate/check soundness lemmas) and root-document lemma_node_shape.

## Reproduce
timeout 120 /tmp/gh-aw/fstar/bin/fstar.exe --smt /tmp/gh-aw/fstar/lib/fstar/z3-4.13.3/bin/z3 --z3version 4.13.3 --z3rlimit 10 --cache_dir /tmp/gh-aw/agent/fstar-audit/w/cache --odir /tmp/gh-aw/agent/fstar-audit/w/out AuditPR11618.fst
F* 2026.09.27, Z3 4.13.3 (pinned release backend).