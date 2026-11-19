# F* audit PR #11604 @ a0b1e6ded71262dfb4a79003fe4a67094171a688

Source: src/ast/rewriter/arith_rewriter.cpp lines 970-995 at head (sha256 of decoded file 5a258e1d7641a7cb454e68e32e108298d3a4d954953b74add736cf07102d8ff4). Base SHA a0d488da9d887aa6a26acd5657bfcf5bce547fae. Tools: F* 2026.09.27, Z3 4.13.3 (pinned release).

## Change
In `mk_and_core`, `a` (numeral of the currently selected bound `a <= y`) is now updated to `b` when a larger bound is found. Before, `a` stayed at the numeral of args[0], so any later bound > a replaced the selection even if weaker than one already selected.

## Obligations (all in AndCoreLowerBound.fst)
1. new_correct: new_scan a a l == max(a, l). PROVED.
2. new_ge: selected bound >= a and >= every bound in the list, so dropping the others is sound (b<=y is implied by m<=y when b<=m). PROVED.
3. old_witness: refutation of the pre-PR code: conjunction (1<=x),(3<=x),(2<=x) yields 2<=x, strictly weaker than 3<=x (a conjunct is lost). CHECKED; new code yields 3. This is a counterexample to the BASE behavior, not to the PR.

## Correspondence
F* models the scan over numerals b of args[i] (i>=1) matching is_le(z,u) with u==y and numeral z. Non-matching args go to `rest` unchanged and are not modelled. Ints stand for rationals (same order). Assumptions: rational comparison is a total order; `u == y` is pointer equality of hash-consed ASTs; mk_and(rest) builds the conjunction. Only the F* standard library is inherited.

## Not covered
AST plumbing, memory safety, rewriting termination under BR_REWRITE1, the `rest.size() < n-1` guard, and src/test/model_evaluator.cpp (test additions; excluded). Semantic model only; C++ execution is not mechanically verified.

## Reproduce
cd /tmp/gh-aw/agent/fstar-audit && timeout 120 /tmp/gh-aw/fstar/bin/fstar.exe --smt /tmp/gh-aw/fstar/lib/fstar/z3-4.13.3/bin/z3 --z3version 4.13.3 --z3rlimit 10 --cache_dir cache --odir out AndCoreLowerBound.fst
