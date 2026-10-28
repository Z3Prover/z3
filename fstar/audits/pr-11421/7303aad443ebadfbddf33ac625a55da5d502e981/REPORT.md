# F* audit, PR #11421 @ 7303aad443ebadfbddf33ac625a55da5d502e981 (base 59e40ee67c58)

**Verdict: proved (partial scope).** One function audited: `fpa2bv_converter::mk_to_fp_real`, symbolic (non-numeral) branch, head lines ~2996-3190 (changed region ~3008-3114). Head differs from previously audited revisions only by merges; the audited C++ diff vs base is identical in the file region above.

## Obligations (Pr11421Head7303.fst), all proved
1. O1 `scale_correct`/`scale_ge1`: the ebits-step bit-conditioned loop (factor 2^(2^i), scale squared) computes exactly 2^(exponent field), and the extra assertions `gap_up >= min_gap` hold.
2. O2 `abs_r_correct`/`range_ok`: abs_r = base + sum bit_i*2^i*gap_up equals the IEEE decoding ((2^k+F)*ulp normal, F*ulp subnormal) and the new exposed bounds base <= abs_r <= base+(2^k-1)*gap_up are valid (k=sbits-1).
3. O3 `pred_dist`/`succ_dist`/`gd_le_gu`: gap_down/gap_up are the true distances to predecessor/successor (incl. binade boundary and smallest-normal case) and the new assertion `gap_down <= gap_up` holds.

No counterexample was found; the obligations were proved directly (no separate refutation witness constructed).

## Correspondence
Integers in units of min_subnormal (min_sub/2 doubling used for integrality); bit fields are `nat -> bool`; `fval`/`scale`/`acc` mirror the C++ loops; `ulp`, `gap_down` mirror `gap_up`/`gap_down` ite expressions.

## Assumptions / not covered
- Real arithmetic modeled over integers scaled by min_subnormal; k>=1, ebits>=1 (sbits>=2).
- Not proved: the rounding-mode conditions (nte/nta/tp/tn/tz), tie handling, overflow constants, signed zero, `is_max_finite` handling, that the fresh-result encoding is equisatisfiable with the old one, incremental-solving behavior (#11375), the test additions in src/test/fpa.cpp. These changed behaviors were excluded (three-function/three-obligation bound).
- Not mechanized: C++ execution, AST plumbing, memory safety, the whole solver. Base-library assumptions: F* standard library only.

## Reproduce
`cd fstar-audit && /tmp/gh-aw/fstar/bin/fstar.exe --smt <z3-4.13.3> --z3version 4.13.3 --include fstar --cache_dir cache --odir out --z3rlimit 10 Pr11421Head7303.fst`
