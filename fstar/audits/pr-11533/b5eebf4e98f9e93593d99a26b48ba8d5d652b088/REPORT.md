# F* audit: PR #11533 (partial scope)
Head b5eebf4e98f9e93593d99a26b48ba8d5d652b088, base 605d1d83a4614804d400ce5b23eca1f4a20184dd.

Changed functions audited (3): `then_simplifier::supports_proofs` (then_simplifier.h), flush-time proof-contract check in `simplifier_solver::flush` (simplifier_solver.cpp ~L168-183), and the `get_proof`/proof-collection fact check (~L319-322).

Obligations (all **proved**):
1. O1 supports_proofs is true iff every child reports true (empty pipeline true).
2. O2/O3 nested then_simplifiers compose as conjunction; one unsupported leaf at any depth yields false.
3. O4 the accept predicate (`pr` non-null and `get_fact(pr) == fml`) holds iff the proof exists and its fact equals the formula; a null proof or mismatched fact (the test's malformed simplifier, checked concretely) is rejected.

No counterexample found. Mapping: bool list = children's supports_proofs; fact abstracted as function on proof ids (expression pointer equality is hash-consed in Z3, assumed).
Assumptions: AST hash-consing makes `!=` on expr pointers semantic-syntactic equality; `m.get_fact` is correct.
Not covered / excluded: constructor-time check in the solver (~L236), the `m_factory` guard conditions, the test file (get_consequences.cpp), exception safety/rollback (test asserts backend has 0 assertions — not formalized), whether proofs themselves are valid (only fact-matching is checked), C++ memory safety. Observation (manual): the flush check runs only when `m_factory` is set, so default pipelines are unchecked; and any custom simplifier that rewrites formulas while keeping a stale proof is rejected (conservative, intended).
Verification: F* 2026.09.27, Z3 4.13.3, rlimit 10, fresh cache. Command: fstar.exe --smt (z3-4.13.3) --z3version 4.13.3 --include fstar --z3rlimit 10 --cache_dir cache --odir out Z3PR11533ProofContract.fst
