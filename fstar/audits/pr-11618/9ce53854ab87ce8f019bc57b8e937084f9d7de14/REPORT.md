## Scope
Head 9ce53854ab87ce8f019bc57b8e937084f9d7de14, base 8573212ffea377844c322487224accff54809594. PR was open at this SHA with no marker comment for it. Audited fstar/Z3SortedRealProduct.fst (214 lines, sha256 779f2f7ac06bcdd2153e902b196773ca8945814d6399a61c7ba0264d6bb60de9), fetched via the contents API at the head SHA. Functions: positive_product, nonpositive_product, check (with candidate).

## Obligations (all proved)
1. positive_product: x>0 and y>0 imply x*y>0 (ob1).
2. nonpositive_product: (x>=0 and y<=0) or (x<=0 and y>=0) imply x*y<=0 (ob2).
3. Refutation shape: facts hold, factor guards hold, p=x*y, and refutation of p>0 imply False (ob3). Only the positive case is modelled.

No witness was sought beyond these; none is established.

## Correspondence and assumptions
Obligations are over FStar.Real and mirror lemma_multiply_positive and lemma_multiply_nonpositive in the PR. They assume LIN.refutes is sound (inherited from base Z3SortedRealLinear, not re-verified), RL.real_laws, and correct Mul classification and scoping. ob3 is an abstract propositional model; it does not mechanically verify lemma_check, nested_candidate fuel bounds, product enumeration, or the C++/OCaml replay. These remain manually reviewed.

## Exclusions
Z3SortedProof.fst (605 added lines: Int product, zero-factor, constant-factor, bounded linear Int replay), Z3SortedRealLinear.fst, Z3SortedRealOrder.fst, Z3SortedRootDocument.fst, all test files, Z3CherryTests.fst, Z3NnfReplay.fst, OCaml/PowerShell/Python tooling, prior audit directories.

## Reproduce
fstar.exe --smt z3-4.13.3/bin/z3 --z3version 4.13.3 --z3rlimit 10 --cache_dir cache --odir out AuditRealProductPR11618.fst
F* 2026.09.27, Z3 4.13.3. No admit, assume, or axioms.