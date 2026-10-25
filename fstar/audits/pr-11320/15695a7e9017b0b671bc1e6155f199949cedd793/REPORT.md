# F* audit: PR 11320 @ 15695a7e9017b0b671bc1e6155f199949cedd793 (base 0f0cb9a4533cede75f0a8ceb35879d2781de8db4)

Trusted tools: F* 2026.09.27; Z3 4.13.3 (pinned release backend under /tmp/gh-aw/fstar/lib/fstar/z3-4.13.3). Not a Z3 built from the PR.

## Changed behavior
src/ast/fpa/fpa2bv_converter.{h,cpp}: new override `fpa2bv_converter_wrapped::mk_uf(f,num,args,result)` (head cpp, new function right after mk_const, ~lines 4785-4795; head file sha256 of fpa2bv_converter.cpp as fetched: 3433d6e5abc3c0446c5e13f018488a1316c63efadbb7f7d8a936c2b6674f4af1). Guards:
- range is float: result = unwrap(wrap(f(args)), range), i.e. fp(extract sgn, extract exp, extract sig) of bvwrap(f(args)).
- range is RM: result = bv2rm(wrap(f(args))), where wrap gives a 3-bit bvwrap.
- else: result = f(args).
Base behaviour (fpa2bv_converter::mk_uf, base lines ~286-330) introduced BV UFs plus quantified bridge axioms (extra_quantify) via m_extra_assertions; the PR avoids these in the wrapped converter, mirroring mk_const/mk_rm_const for constants.

## Obligations (module Z3FpaWrappedUf11320.fst)
- O1 (proved): for ebits,sbits>=2 and any w < 2^(ebits+sbits), concat(sgn,exp,sig) of the three extract fields used by unwrap equals w. So unwrap/wrap is a lossless bit-level decomposition of the wrapped value (same extraction as mk_const).
- O2 (proved): field widths 1 + ebits + (sbits-1) = ebits+sbits (matches SASSERT in unwrap).
- O3 (proved): RM unwrap ite-chain decodes codes 0..4 (BV_RM_TIES_TO_EVEN=0, TIES_TO_AWAY=1, TO_POSITIVE=2, TO_NEGATIVE=3, TO_ZERO=4) back to the right mode, and maps 5..7 to RTZ (total). Round-trip with code() holds.

Counterexample search: no witness was found for these obligations; none of them is refutable, and the obligations are consistent with the C++ guards. A failed proof was not treated as a counterexample.

## F* to C++ mapping
extract(hi,lo,x) = (x / 2^lo) mod 2^(hi-lo+1) models mk_extract on a BV numeral. concat3 models mk_concat/join. unwrap_rm models the nested ite on BV_RM codes. BV values are modelled as naturals below 2^w.

## Assumptions
Standard F* ulib (Prims.pow2, FStar.Math.Lemmas) only; no base fstar/ modules imported, no admit/assume/lax. Source semantics of bvwrap as an uninterpreted BV-valued wrapper is assumed (theory_fpa handles it), and was not modelled.

## Not covered (manually reviewed / excluded)
- test changes in src/test/fpa.cpp (3 tests): not proof targets.
- fpa2bv_converter.h declaration: plumbing.
- Interaction with theory_fpa relevant_eh/NaN canonicalization (cf. base Z3FpaNanWrap.fst/Z3FpaNanCongruence.fst), MBQI instantiation, model construction, and whether bvwrap(f(args)) with bound variables is correctly treated by quantifier machinery. Note in the base, NaN payload multiplicity via wrap is a known concern; the PR tests (test_mbqi_nan_arrays, test_nan_datatype_congruence) target it but were not verified here.
- Memory/ref-counting, AST plumbing (app_ref temporaries look fine on read).
Semantic proofs here are not mechanized verification of C++ execution.

## Reproduce
mkdir cache out; timeout 120 /tmp/gh-aw/fstar/bin/fstar.exe --smt /tmp/gh-aw/fstar/lib/fstar/z3-4.13.3/bin/z3 --z3version 4.13.3 --include fstar --z3rlimit 10 --cache_dir cache --odir out Z3FpaWrappedUf11320.fst