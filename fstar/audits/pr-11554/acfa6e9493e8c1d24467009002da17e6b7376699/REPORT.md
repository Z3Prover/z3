# F* audit PR 11554 @ acfa6e9493e8c1d24467009002da17e6b7376699 (base 784b613b57cde61abf05fdbd52fa861195de9acb)

Delta since last audited head 86cec18 is large (about 60 files); the previous audit covered only ITE laws. Pre-checks: PR open, head matches, no existing fstar-nfv-audit comment for this SHA.

## Source snapshot
src/ast/rewriter/arith_swine.cpp sha256 87dfed234ae77fb835923018a4cd56da2e6d3b36853ca9bfeec697de1fdc98f1; arith_swine.h sha256 18ab0fac96d017946e779cae133a3b24842661ec5b58da600b4aec64f2b5d7df (fetched via contents API at head SHA, stored under /tmp/gh-aw/agent/src). Also read: mpz_manager::bitsize (src/util/mpz.cpp ~2268: log2(a)+1 for nonneg, mlog2(a)+1 otherwise).

## Obligation O1 (proved)
Source guard: in check_model, `p.y >= 0 && abs(p.x) >= 2 && p.y > p.value.bitsize()+1` returns l_false (power constraint violated). Intended property: under that guard x^y != value, so refuting the candidate model is sound. F* module SwinePowAudit: pow_ge (|x|>=2 implies |x^n| >= 2^n) and early_reject_sound (y>=0, |x|>=2, y>bs+1, |v|<=2^bs implies pow x y <> v). Mapping: p.x,p.y,p.value -> x,y,v as unbounded ints; bitsize -> bs with assumption |v|<=2^bs (follows from the log2+1 definitions; inherited from reading mpz.cpp, not mechanized).

## Not selected (budget: 3 functions x 3 obligations)
Candidates reviewed but not proved: compute_power (negative-exponent convention: returns 0 for y<0,|x|>=2, which assumes the integer-power semantics 0 there; abstains on overflow budget returning false -> l_undef path), check_real_power, real_power_axioms (even-denominator/negative-base axioms). These are inconclusive/unaudited, not evidence of safety. All other changed files (rewriters, LRA/NLA solver changes, purify_arith, demodulator, tests, python API, existing fstar proofs) are excluded.

## Limits
Semantic model only; no mechanization of C++ execution, memory safety, rational/mpz implementation, or whole-solver soundness. No counterexample was sought beyond a manual read; none found for O1.

## Reproduce
fstar.exe --smt /tmp/gh-aw/fstar/lib/fstar/z3-4.13.3/bin/z3 --z3version 4.13.3 --z3rlimit 10 --include fstar --cache_dir cache --odir out SwinePowAudit.fst (120 s timeout). F* 2026.09.27, Z3 4.13.3.