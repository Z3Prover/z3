# F* audit PR #11634 @ 35207943f33b296cde51305c9f737046df208b86 (base 8927ff98ea8eae56021f8e8ea874a9465ea6a257)

Scope (partial): `context::get_lower_value` and `context::get_upper_value`, case O_MAXSMT, in src/opt/opt_context.cpp (lines 2327-2362 at head). Head file sha256 e8c39414f0bd1e2d16f248903a919751e5fd2efa451d1c8dc44e57166956c0e3; base file sha256 3ad24dd268d390d97018f9ede23dd8eaa65cd6095049b3b1541abe4103b5d4e5.

## Correspondence
`maxsmt::get_lower/get_upper` (maxsmt.cpp 260-276) return the raw bound passed through `adjust_value` (negate then add offset). With negate, this maps raw lower to an adjusted upper, so base `get_lower_value` could return a value greater than `get_upper_value`. The PR swaps the two when `get_negate()` is true. F* integers model rationals; `adjust`, `ms_lower`, `ms_upper`, `base_*`, `pr_*` mirror these.

## Obligations (all proved)
1. ob1: lo<=hi implies pr_lower <= pr_upper for any offset/negate.
2. ob2: any raw v in [lo,hi] has adjusted value within [pr_lower, pr_upper].
3. ob3: for negate=false, head equals base.
Also checked: base_cex, a concrete witness (lo=0, hi=1, off=0, neg=true) where base yields lower>upper (this refutes the base, confirming the bug fixed; head is well-formed on the same witness).

## Assumptions / not covered
Raw m_lower<=m_upper is assumed (ob1/ob2 premise); infinities/epsilons (inf_eps, objective_value) not modelled; the O_MINIMIZE/O_MAXIMIZE branches (unchanged), update_bound (line 2211-2231 context only), the new test in src/test/opt_bounds.cpp, C++ execution, memory safety are excluded and manually unreviewed. Whether m_lower<=m_upper holds in all solver states is not proved. Only the unchanged-by-PR `maxsmt` semantics were read, not mechanised. No base modules imported; only F* core library.

## Reproduce
cd fstar-audit; see cmd.txt. F* 2026.09.27, Z3 4.13.3 (bundled).
