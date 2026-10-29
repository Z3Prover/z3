# F* audit PR 11421 @ add0605bbfcfc9b06e7264dbbb837992b24d11cc (base cec57fc8)

PARTIAL scope. Changed function audited: `fpa2bv_converter::mk_to_fp_real` symbolic branch in src/ast/fpa/fpa2bv_converter.cpp (head blob sha256 of fetched file 67ef8042feb06aa97869ed2154a1fe56140eb80fc2d7ecb644533111eef2b7eb, lines ~3000-3115). Only this one function, three obligations.

## Obligations (all **proved** in Pr11421Linear.fst)
1. ULP encoding: the conditional-constant-multiplication loop (factors 2^(2^i) for bit i of the exponent field, `scale *= scale`) equals 2^(exponent value); with the `exp_is_zero` ite, gap_up = min_subnormal*2^(e-1) for e>=1 and min_subnormal for e=0 (`scale_correct`, `gap_up_matches`).
2. Magnitude encoding: abs_r = ite(e=0,0,hidden*gap_up) + sum_i bit_i*2^i*gap_up equals the IEEE decoded magnitude (hidden+F)*ulp / F*ulp, and the newly exposed bounds base <= abs_r <= base+(2^k-1)*gap_up are valid (`abs_r_correct`, `range_ok`, `fval_bound`).
3. Neighbour gaps: gap_up is the exact distance to the next-larger-magnitude float (including binade rollover), gap_down per the C++ guard (e=0 || e=1 || sig!=0 -> gap_up else gap_up/2) is the exact distance to the predecessor (including subnormal/min-normal and power-of-two boundaries), and the new assertion gap_down <= gap_up holds (`succ_dist`, `pred_dist`, `gd_le_gu`).

No counterexample was found/attempted successfully: the refutation attempt (searching for guard-satisfying inputs violating these properties) failed because all were proved.

## Correspondence / assumptions
Integers scaled by min_subnormal replace reals (exact, since all quantities are integer multiples of min_subnormal; for C++ the e=0 gap_up/2 initial value is only used in the multiplicative path and replaced by ite). Bit fields are modelled as nat->bool; k = sbits-1 >= 1; ebits arbitrary (exponent value ev up to 2^ebits-1). Inherited: F* stdlib and Z3 4.13.3 backend. No admit/assume/axioms.

## Not covered (manually reviewed only / excluded)
- Five rounding-mode conditions, tie logic, is_max_finite, overflow/inf implications, sign constraints (unchanged logic, not re-proved; they now consume the verified gap/magnitude values).
- Equivalence of removing `round(...)`/fp.to_real: relies on the rounding relation uniquely determining result; not mechanized. Relatedly, completeness of the relation (a rounding exists for every x) was not proved.
- Zero result sign cases and NaN/inf exclusion semantic details; m_extra_assertions plumbing, Z3 AST construction, memory safety, and arithmetic solver behaviour.
- src/test/fpa.cpp (47 added lines), and the PR's added `fstar/audits/pr-11421/4f554c5f.../` files (an earlier audit bundle; not audited).
This is a semantic model, not mechanized verification of C++ execution.

## Reproduce
fstar.exe --smt /tmp/gh-aw/fstar/lib/fstar/z3-4.13.3/bin/z3 --z3version 4.13.3 --include fstar --z3rlimit 10 --cache_dir cache --odir out Pr11421Linear.fst
