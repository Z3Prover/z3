# F* audit of PR #11571 @ a9983a98da2eae4386c0366eb666f27731dd7f02 (base f82ed971015584fbdfb5723e4e529abe3fff6b5c)

Verdict: **inconclusive** (partial scope).

## Scope
PR changes only proof engineering in fstar/ (no C++/production semantics): Z3SortedProof.fst (3 new scoped-helper lemmas + call sites), Z3NnfReplay.fst (lemma_all_hold_four + call sites), Z3SortedProofTests.fst and Z3SortedRootDocumentTests.fst (assert_norm -> nbe tactic; one new expect_failure test).
Selected (<=3 functions): lemma_scoped_binary, lemma_scoped_ternary, lemma_scoped_quantifier_pair.
Excluded: lemma_all_hold_four, modified lemma_congruent / lemma_quantifier_equality / lemma_ite_ok / lemma_iff_ok bodies, and all test-file changes (not checked).

## Obligations
1. lemma_scoped_binary: scoped(App f [x;y]) => scoped x /\ scoped y. 
2. lemma_scoped_ternary: analogous for 3 args.
3. lemma_scoped_quantifier_pair: scoped [] (App f [Q..a; Q'..b]) => both quantifiers scoped and bodies scoped under rev bs @ [].
Result: all three checked, but only against an ABSTRACT model (Z3PR11571ScopedModel.fst) that keeps the structural recursion of Z3Definitions.scoped/scoped_args and replaces sorts_match / quant_sort / var side conditions by an arbitrary parametric record of predicates (no axioms). Lemmas hold for every such predicate choice.
The same lemmas against the real base Z3Definitions could not be checked: base module Z3List.fst fails to load with the pinned F* (custard_inline missing), a toolchain mismatch unrelated to the PR. Hence inconclusive, not proved. Other changes are soundness-neutral in intent (helpers only supply facts derivable from the scoped definition) but unchecked here.

## Not mechanized
C++ execution, AST plumbing, memory safety; the correspondence to the real expr/sort types is manual. No counterexample was sought beyond observing the lemmas are consequences of the definition's conjunctive recursion.

## Reproduce
/tmp/gh-aw/fstar/bin/fstar.exe --smt /tmp/gh-aw/fstar/lib/fstar/z3-4.13.3/bin/z3 --z3version 4.13.3 --include /home/runner/work/z3/z3/fstar --z3rlimit 10 --cache_dir cache2 --odir out2 Z3PR11571ScopedModel.fst