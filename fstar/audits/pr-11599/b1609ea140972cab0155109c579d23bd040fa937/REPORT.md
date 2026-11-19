# F* audit of PR #11599 @ b1609ea140972cab0155109c579d23bd040fa937

Scope (partial): `algebraic_manager::compare_core` same-polynomial branch in `src/math/polynomial/algebraic_numbers.cpp` (one changed function). Excluded: test changes in `src/test/algebraic_numbers.cpp`, the rest of compare_core (minimal-polynomial / refinement / sign paths), `update_sign_lower`, refinement, memory safety.

Source hashes (decoded from contents API, sha256): head 0eeef829496c3211b31f36a79a3eb17876473f38adf7c518fc7cb7d9b6cbe8e6, base (6df87c115cb08dc05e4126d432dbab007e23f5c3) 45d4e6704727e48585a3cab441c422eff969d3309423ead25d43e4e9383be87a. Head lines ~2086-2107 (COMPARE_INTERVAL, compare_p branch).

Tools: F* 2026.09.27, Z3 4.13.3 (pinned release backend).

## Model
Squarefree p has simple roots r0<...<r(n-1); `cnt x` = roots below x. Isolating cell (l,u): l,u not roots, cnt u = cnt l + 1, so its root is r(cnt l). `m_sign_lower` = sign of p(l) = parity of cnt l (sign flips at each simple root). Reaching the compare_p branch means COMPARE_INTERVAL did not fire, i.e. intervals overlap (not a.u<=b.l, not a.l>=b.u).

## Obligations (all proved)
1. `ob1`: overlapping isolating cells of the same polynomial have equal lower sign iff they contain the same root. (Roots idx differ by at most 1 under overlap, so parity separates.)
2. `ob2`: head's result (`Zero` if equal lower signs, else order by lower endpoints) equals the true comparison of the two roots.
3. `witness`: refutation of the BASE behavior (always Zero): concrete reachable overlapping cells (-5,5) and (3,12) with roots 0,10 satisfy all guards, base returns Zero but true order is Neg; head returns Neg. This refutes base, not the PR head.

## Assumptions
- p squarefree with simple roots (cells in Z3 come from squarefree/factored polynomials; the SASSERT in update_sign_lower asserts opposite signs at endpoints), roots modelled over integers (ordering only matters); sign_lower faithfully reflects parity of roots below lower; cells are isolating invariants (acell_inv). `upm().eq` for compare_p is taken as polynomial equality. Not mechanized: C++ execution, mpbq arithmetic, upm sign evaluation, the other branches. Assumptions are properties in lemma preconditions, not axioms; no admit/assume.
- Caveat: m_sign_lower must be up to date after refinement (refine keeps sign_lower consistent by C++ review not mechanized).

## Reproduce
```
mkdir cache out
timeout 120 /tmp/gh-aw/fstar/bin/fstar.exe --smt /tmp/gh-aw/fstar/lib/fstar/z3-4.13.3/bin/z3 --z3version 4.13.3 --include fstar --z3rlimit 10 --cache_dir cache --odir out Z3AlgebraicRootCompare.fst
```
