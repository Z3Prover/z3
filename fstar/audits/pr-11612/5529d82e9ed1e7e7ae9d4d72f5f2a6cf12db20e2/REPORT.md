# F* audit PR 11612 @ 5529d82e9ed1e7e7ae9d4d72f5f2a6cf12db20e2 (base ff86ba7d1793b0ffcba6848cc30c039b07a55568)

PR is open at this head; no prior fstar-nfv-audit comment for this SHA. The PR is proof-maintenance only (F* files and test tools); no C++ solver code changed, so this is not a semantic audit of C++.

## Obligations (all proved)
1. ob1: in Z3RealPower.power, the negative-base branch (x<>0, not x>0) implies 0-x>0 (the new negated_base_positive call precondition holds).
2. ob2: signed p a == a for even p (signed_even).
3. ob3: power with the added ghost call equals the old definition for any abstract pow and classifier (PR does not change the value of power; pow abstracted, which is sound since the call is ghost-only).
4. ob4: lemma_concat_number (Z3BvFreshModel/Z3BvWord) value transport v=l*p+r.
5. ob5: lemma_split_numeral (Z3BvWord): for p>0, 0<=y<p, x*p+y==n iff x==n/p and y==n%p.

## Correspondence
Self-contained model Z3AuditPr11612.fst copies the definitions/lemma statements from PR head source (Z3RealPower.fst blob fetched via contents API, sha256 of decoded file 4ff833198224a1c1d75cb42e9c61ae421061c2c1e23a062d975c3744be6b1d38; lines ~168-190). FStar.Math.Pow and the classifier are abstracted (classifier outcome parameter, pow as function parameter). No base modules imported, no admits/assumes/lax. Inherited assumptions: F* standard library (FStar.Real, FStar.Math.Lemmas).

## Exclusions (not audited)
Diffs scanned for admit/assume/lax/axiom/#set-options bypass patterns: none added. Not audited: Z3BvFreshModel lemma_bv_model_intro/lemma_concat/lemma_bv_model; Z3BvLemma lemma_subtraction_rewrite; Z3CherryTests; Z3LinearArithmeticEmbed; Z3NnfReplay; Z3QuantIntroCounterModelTests; Z3SortedArithmetic; Z3SortedDatatype; Z3SortedDependentSkolem; Z3SortedProof; Z3SortedSkolem; Z3TypedRootTests; tools/test_native_bridge.ml; tools/test_native_checker.py. Whether the PR files themselves verify (including solver stability) was not checked; PR code was not executed.

## Reproduce
timeout 120 /tmp/gh-aw/fstar/bin/fstar.exe --smt /tmp/gh-aw/fstar/lib/fstar/z3-4.13.3/bin/z3 --z3version 4.13.3 --include /home/runner/work/z3/z3/fstar --cache_dir cache --odir out --z3rlimit 10 Z3AuditPr11612.fst
Run in an empty directory with Z3AuditPr11612.fst and fresh cache/out dirs.