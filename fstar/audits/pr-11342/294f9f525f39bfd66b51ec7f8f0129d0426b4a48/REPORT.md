## Scope
PR #11342, head 294f9f525f39bfd66b51ec7f8f0129d0426b4a48, base e7cfef8b. Changed: fstar/Z3BvLemma.fst (simple, lemma_nat_lt_pow2, lemma_lshr_self, lemma_simple), Z3BvWord.fst (z3rlimit 200 on lemma_append_number), tools/test_native_bridge.ml (tests).

## Obligations (AuditLshrSelf.fst)
1. PROVED: for all width>0 and a in uint_t width, U.shift_right a a == 0 (including a >= width). Uses a < pow2 a, shift_right_value_lemma, small_division_lemma_1.
2. PROVED: instances at width 8 and 65 plus concrete 200>>200 == 0 at 8 bits.
3. PROVED: the analogous bvshl x x -> 0 is invalid (1<<1 = 2 <> 0 at 8 bits), so the PR correctly omits it. (Test expects false.)

## Correspondence
Base Z3BvLemma.calculate maps op_lshr to U.shift_right x y, with unsigned semantics (shift >= width yields 0). The new guard x = y && op = op_lshr returns literal width 0, matching the C++ rewriter (bvlshr x x -> 0). The guard is placed before the and/or rule; op_lshr is disjoint from op_and/op_or/op_xor/op_sub so no existing rule is shadowed.

## Assumptions
Base FStar.UInt and FStar.Math.Lemmas library lemmas; the model of calculate is taken from base. Standalone module restates the lemmas rather than importing PR code.

## Exclusions / not checked
The PR modules themselves were not run (trust boundary: PR code not executed). lemma_append_number rlimit increase (a proof-budget change, no semantic effect), OCaml tests, C++ execution, memory safety.

## Versions
F* 2026.09.27; Z3 4.13.3.

## Reproduce
fstar.exe --smt /tmp/gh-aw/fstar/lib/fstar/z3-4.13.3/bin/z3 --z3version 4.13.3 --z3rlimit 10 --cache_dir cache --odir out AuditLshrSelf.fst  (exit 0)