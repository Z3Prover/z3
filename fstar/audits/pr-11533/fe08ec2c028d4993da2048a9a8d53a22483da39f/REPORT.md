## F* audit of PR 11533 @ fe08ec2
F* 2026.09.27, Z3 4.13.3 (pinned backend), z3rlimit 10.

### Obligations (all proved)
1. then_simplifier.h supports_proofs = all_of children: O1 (iff all children true), O2 (append), O3/O3b (nested then and one unsupported leaf at any depth gives false).
2. simplifier_solver.cpp flush check (`!pr || get_fact(pr) != fml` throws): O4 no throw iff each flushed formula has a proof with fact exactly equal to it; O5 concrete witnesses (not(a) with a proof, and dropped proof) are rejected.
3. Factory guard (`m_factory && proofs_enabled && !supports_proofs` throws): O6 truth table.

### Correspondence
bool lists model child supports_proofs flags; fact is an abstract function on proof ids; formulas are ints. Base default supports_proofs()=false (dependent_expr_state.h:250) is assumed from source; ast hash-consing makes pointer inequality equal expression inequality (assumed, manual).

### Assumptions/exclusions
No admits or axioms; only FStar.List.Tot. Excluded: get_consequences.cpp test, the get_proof/m.get_fact check at line ~319 (same shape as O4), exception propagation/state rollback, memory safety, whether each leaf simplifier truly reports supports_proofs honestly. This is a semantic audit, not C++ verification.

### Reproduce
`mkdir cache out; fstar.exe --smt z3-4.13.3/bin/z3 --z3version 4.13.3 --include fstar --z3rlimit 10 --cache_dir cache --odir out Z3PR11533Audit.fst`