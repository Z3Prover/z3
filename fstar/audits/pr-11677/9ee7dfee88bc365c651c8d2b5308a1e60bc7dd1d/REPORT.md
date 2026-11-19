# F* audit PR 11677 @ 9ee7dfee88bc365c651c8d2b5308a1e60bc7dd1d (base d72de58d9e36009f1397377cd185342474c8ecfb)

Head src/math/lp/monomial_bounds.cpp fetched via the contents API; decoded sha256 977fc4080eef71b2c28e18a9744a28d682013fee77d119bbd7c2702ed3c74e09.
Tools: F* 2026.09.27, Z3 4.13.3 (pinned release backend).

## Obligations (all proved)
1. `bounded_root` (head lines 20-26): returns the original `root` result or abstains; abstains only if p>1 and (p>256 or bitsize>256). p=1 is never skipped; 256 bits / 256 factors are still processed, 257 skipped. Optional propagation is only dropped, never altered, so emitted bounds keep their soundness. Used at 6 call sites (~lines 733-798).
2. `tighten_lp` guard (~lines 129-136): early `return false` (no tightening) if m.size()>256 or any existing bound of a factor exceeds 256 bits; otherwise the body is unchanged. Skipping is sound because the function only strengthens LP bounds and emits no lemmas.
3. Reordering `check_monic` after `is_linear` (~line 320): `chk || !lin` equals `!lin || chk`, so the skip condition is identical; check_monic is now evaluated only for linear monics (cost saving; assumes check_monic is side-effect free).

## Correspondence
F* models guards as pure predicates over bit sizes and factor counts; `root_orig` is an abstract function standing for rational::root (no axioms). bitsize() and m.size() are modelled as nat.

## Assumptions / manual review only
rational::bitsize semantics, check_monic purity, C++ execution, memory safety and LP state are not mechanized. That 256 suffices to avoid the timeout in #11643 is a performance question, not proved. The tighten_lp guard inspects only factor bounds, not m.var() bounds or derived interval growth; up to 256 factors of 256-bit values can give products of ~65536 bits: bounded, not eliminated.

## Exclusions
src/test/monomial_bounds.cpp (test_bounded_roots) not audited; is_too_big constant refactor (trivial); other callers and generate_lemma paths unchanged and unreviewed.

## Reproduce
Run from a directory containing PR11677MonomialBounds.fst (fresh cache/odir):
timeout 120 /tmp/gh-aw/fstar/bin/fstar.exe --smt /tmp/gh-aw/fstar/lib/fstar/z3-4.13.3/bin/z3 --z3version 4.13.3 --z3rlimit 10 --include /home/runner/work/z3/z3/fstar --cache_dir /tmp/gh-aw/agent/fstar-audit/cache --odir /tmp/gh-aw/agent/fstar-audit/out PR11677MonomialBounds.fst
