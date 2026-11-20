# F* audit PR #11700 @ 0dd4af3078d462c35ecb5a31366c5f341aa93a61 (base 1a1d88dde7cc567e2ed6beeea05321aa5a223c8a)

Partial scope. Head polynomial.cpp blob 676f53cb (fetched via git blob API, sha256 of decoded file 2f2c5b5c...ef130ab, 8356 lines).

## Selected function (1 of 3 allowed): `imp::arithmetic_checkpoint` (polynomial.cpp lines 2578-2585)
Intended property: when charging is enabled, each coefficient operation charges at least 1 and at most UINT_MAX rlimit units, scaled by operand word sizes, without unsigned underflow/overflow.
Obligations (module `ArithCharge.fst`):
1. O1 (proved): bitsize>=1 so `(bitsize-1)` has no unsigned underflow, words>=1. Source: mpz::bitsize returns log2+1 >= 1 for nonneg and mlog2+1 >= 1 otherwise (mpz.cpp 2268-2273).
2. O2 (proved): clamped charge in [1, UINT_MAX], so the `unsigned` cast is exact.
3. O3 (proved): charge monotone in operand bit-size; sample values 1x1 -> 1, 4097-bit x 4097-bit -> 129*129.
No counterexample sought succeeded; none found.

## Mapping / assumptions
F* uses mathematical ints for bitsize, words, product; C++ uint64 product of two unsigned words never overflows (each <= 2^27+1, product < 2^55). Assumes `reslimit::inc(unsigned)` adds offset to uint64 m_count (rlimit.cpp 46-49, read manually). Inherits F* stdlib (FStar.Math.Lemmas) and Z3 4.13.3 trust.

## Reviewed manually, not mechanized (exclusions)
- `scoped_arithmetic_charge` RAII (resets som buffers when unwinding via std::uncaught_exceptions; nested restore of m_old). Looks consistent; not proved.
- `ic()` rewritten gcd loop under charging: sets a=|p[0]|, loops gcd with early stop at 1; equals mpz gcd(sz, as) semantically; not proved (gcd result nonneg since gcd(a,b) yields nonneg). Edge: the sz>=2 non-const case handled; early exit when a==1 is sound.
- Added checkpoints in mul/addmul loops, content gcd, div, pseudo_division_core, resultant, tests (opt_bounds.cpp, polynomial_factorization.cpp), `#include <exception>`.
- Observation: checkpoint is placed before the operation, so arithmetic with huge operands is charged but still executed once; cancellation granularity is per coefficient operation. m_count is uint64 so large charges can't wrap.
- Not covered: C++ execution, memory safety, whole solver, the optimization (curve certificate) change in tests.

## Reproduce
```
F=/tmp/gh-aw/fstar; fstar.exe --smt $F/lib/fstar/z3-4.13.3/bin/z3 --z3version 4.13.3 --include fstar --z3rlimit 10 --cache_dir cache --odir out ArithCharge.fst
```
F* 2026.09.27, Z3 4.13.3. Exit 0, "All verification conditions discharged successfully".
