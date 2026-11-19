## Scope
Changed functions audited: (1) integer_product_clause_equality / integer_clause_equality_witness, (2) integer_product_clause (new disjunct), (3) lemma_integer_product_clause_equality / lemma_clause_complements_except.
Excluded: Z3CherryTests.fst, Z3SortedRootDocumentTests.fst, tools/test_native_bridge.ml (tests only), the lemma_integer_product_clause dispatch edit, product_equality_clause_facts, all C++ and OCaml extraction plumbing.

## Intended property
A clause is accepted if some literal e is an Int equation whose product-equality check passes under the facts plus the negations of all other literals (filter t <> e). The clause is then true in every model of the facts.

## Obligations (abstract model PRClauseEqualityAudit.fst)
- O1 step_sound: if e is in lits, every other literal is false and e holds, then the clause holds, including duplicate occurrences of e. PROVED.
- O2 clause_false_all: a false clause makes every literal false, so complements of the non-e literals are true facts. PROVED.
- O3 example_arith: x<=2 and x>=2 imply x*y=2*y over Int. PROVED.
- Control: without the guard the clause can be false. Checked.
Refutation attempt: O1 holds universally, so no witness exists in the model.

## Correspondence and limits
The model abstracts expressions to literals under a valuation and L.filter to an others-false premise. It does not import PR proof modules, so it does NOT verify the actual F* lemmas. Those need the PR build harness, which was not run per policy. Budget guards (facts<=29, total<=30, arguments_budget 4096) and D.scoped checks were not modelled. Not verified: C++ execution, AST plumbing, memory safety, the solver. The verdict is inconclusive because the real lemmas were not checked.

## Assumptions
Standard F* library only; Boolean semantics of Or; Int arithmetic from the SMT backend. No admit or assume.

## Reproduce
See the verification log. F* 2026.09.27, Z3 4.13.3 (pinned release backend).
