# F* audit PR #11421 head c8a8ba09 (partial scope)

## Audited function (1 of 3 allowed)
`fpa2bv_converter::mk_to_fp_real`, symbolic-x branch (src/ast/fpa/fpa2bv_converter.cpp @ c8a8ba096f78b1624454236504ce029651f7c000, decoded sha256 67ef8042feb06aa97869ed2154a1fe56140eb80fc2d7ecb644533111eef2b7eb, lines ~2997-3208), newly rewritten ULP/magnitude encoding (lines ~3060-3100).

## Obligations (all proved; no counterexample found)
1. O1 `o1_gap`/`o1_ulp`: the exponent loop (gap *= 2^(2^i) when bit i set, start min_subnormal/2) computes 2^(e mod 2^k); with the exp_is_zero ite, gap_up = min_subnormal * 2^(max(e,1)-1) (ULP). Units: min_subnormal/2 = 1.
2. O2 `o2_frac`/`o2_value`: the conditional linear sum of fraction bits plus hidden-bit base equals the IEEE magnitude (subnormal f; normal (2^(sb-1)+f)*2^(e-1)) for every e<2^eb, s<2^(sb-1).
3. O3 `o3_bounds`: the new extra assertions (gap_up >= min_gap at each loop step, implied by gap >= 1; abs_r >= base; abs_r <= base+(2^(sb-1)-1)*gap_up) are valid, so they do not exclude any legitimate float.

## Correspondence and assumptions
F* models the C++ loops over naturals (bit k = (x/2^k)%2) in exact integer units. Mapping from Z3 AST ops (extract, ite, mk_mul by numerals) to these definitions is manual review. Assumptions: F* standard library and Z3 4.13.3. Reals are modeled by naturals scaled by min_subnormal/2.

## Exclusions (not audited)
rounding_cond (nearest/away/to-zero, ties, gap_down), overflow/infinity implications, zero handling, the constant-numeral branch, mk_to_fp_real_int, tests in src/test/api.cpp and src/test/fpa.cpp, memory safety, AST plumbing, solver behavior. Not a verification of C++ execution.

## Reproduce
See verification.log; module Pr11421Head.fst has no admits/assumes.