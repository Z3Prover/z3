# F* audit: PR #11599 @ 1730589187ba8de9d7a294e7b7ed1ddefa295082 (base 6df87c115cb08dc05e4126d432dbab007e23f5c3)

Scope (partial): one changed function, `algebraic_numbers::manager::imp::compare_core`, same-polynomial overlap branch (src/math/polynomial/algebraic_numbers.cpp, lines ~2086-2106 at head). Head file sha256 (decoded contents API) 0eeef829496c3211b31f36a79a3eb17876473f38adf7c518fc7cb7d9b6cbe8e6; base 45d4e6704727e48585a3cab441c422eff969d3309423ead25d43e4e9383be87a.

Obligations (module Z3AlgRootCmp11599.fst):
1. `new_correct` — PROVED: for two isolating cells of one polynomial with overlapping intervals, the new code (equal sign_lower => 0, else order by lower endpoints) returns the true order of the roots.
2. `cheap_correct` — PROVED: the preceding COMPARE_INTERVAL exits are correct for isolating cells.
3. `old_wrong` — checked concrete witness (roots 8 and 12, cells (6,10), (9,14), sign pattern +,-,+): the base code returns "equal" for distinct roots; the new code returns "less". This confirms the bug fixed by the PR; it is not a counterexample to the PR.

Mapping: cell = (lower, upper, root); `sg` = sign of the polynomial (0 at the root); `isolating` = exactly one root in the interval with sign change at it, and sign at lower equals m_sign_lower (invariant acell_inv, maintained by update_sign_lower/normalize_coeffs/refine). Equality of polynomials (compare_p) is assumed to be the premise of the branch.

Assumptions: the sign_lower invariant holds and the lower endpoint is not a root; interval endpoints are totally ordered (mpbq lt/le/ge exact); the polynomial has no other root in either interval (isolating). Intervals are modelled over int (ordering only); sign pattern modelled abstractly via a function. Standard library only; no base modules imported.

Exclusions: the rest of compare_core (different-polynomial path), the new unit test in src/test/algebraic_numbers.cpp, and C++ execution, memory safety, mpbq arithmetic, and refinement code are not mechanically verified. Previous audit comment for SHA b1609ea... is for an earlier head and was not reused.

Reproduce: fstar.exe --smt z3-4.13.3/bin/z3 --z3version 4.13.3 --include fstar --z3rlimit 10 --cache_dir cache --odir out Z3AlgRootCmp11599.fst
