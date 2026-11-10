## Scope
Head ced7906ab6c46fa46649f0a2b31da84aa9553f01, base 8573212ffea377844c322487224accff54809594. PR open at that SHA; no prior fstar-nfv-audit comment found.
Fetched fstar/Z3SortedRealProduct.fst at head (sha256 5bcfcea145ac34e90f283a6df889c717f116aead94154391d943bdf23550753c; blob 79a2c411).

## Obligations (function: positive_product / nonpositive_product, rule soundness)
1. positive_product: x>0 and y>0 imply x*y>0 - **proved** (AuditRealProduct.positive_product).
2. nonpositive_product: one factor >=0 and the other <=0 imply x*y<=0 - **proved**.
3. Contradiction forms: facts entailing p=x*y with the opposite sign are inconsistent - **proved** (contradiction_pos, contradiction_nonpos).
No counterexample sought succeeded; none exists for these arithmetic facts.

## Correspondence
The F* model mirrors the guards in positive_product (both factors refuted when non-positive, product refuted when positive-negated) and nonpositive_product (bound true x with bound false y, or the swap; then p>0 refuted). It does NOT model LIN.refutes, candidate search, fuel/budget limits, the AST (Mul arity, scoping), or the OCaml extraction/native checker.

## Assumptions
Standard F* Prims/FStar.Real axioms and the Z3 4.13.3 backend. The PR checker semantic lemmas (lemma_positive_product, lemma_nonpositive_product, lemma_check) are not imported or re-verified here; they were not run against trusted base modules.

## Exclusions
Z3SortedProof.fst (+364), Z3CherryTests, Z3NnfReplay, Z3SortedRealLinear/Order, RootDocument(+Tests), RealDocumentTests, RealProductTests, all tools/OCaml/Python changes, including the Int product rules, bounded linear Int unit consequences, and Real equality reconstruction. Coverage claims in the PR body (pending applications 2454 to 1952) were not checked.

## Reproduce
fstar.exe --smt /tmp/gh-aw/fstar/lib/fstar/z3-4.13.3/bin/z3 --z3version 4.13.3 --z3rlimit 10 --cache_dir cache --odir out AuditRealProduct.fst
F* 2026.09.27, Z3 4.13.3. Exit code 0.