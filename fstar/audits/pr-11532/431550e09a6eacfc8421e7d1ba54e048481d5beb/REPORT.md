# F* audit, PR #11532 @ 431550e09a6eacfc8421e7d1ba54e048481d5beb (base 605d1d83a4614804d400ce5b23eca1f4a20184dd)

Source: src/tactic/arith/purify_arith_tactic.cpp, head sha256 0c97448a55522ac7cf1a904c120681238e7fd597c4c30a424032b63f63dac068 (base 743d1e4c...). Fetched via contents API; not executed.

## Scope (partial, 3 functions)
1. process_idiv / process_mod (head lines ~358-423, ~415-424): process_mod now builds an idiv app (div x y) instead of passing the mod decl to process_idiv.
2. Shared congruence assertions (assert_congruences, ~lines 844-866): th-lemma with both defining proofs as premises.
3. process_power zero-exponent (~455-490) shared 0^0 variable proofs.

## Obligations (PurifyArithAudit.fst)
- O1 `o1_unique` (proved): for y<>0 the constraints pushed by process_idiv (x = k1*y+k2, 0<=k2, y<=0 \/ k2(y, y)=0 \/ k2 < -y) determine k1,k2 uniquely.
- O2 `o2_exists` (proved): for y<>0 a solution exists (Euclidean division incl. negative y), so introducing k1,k2 is satisfiability preserving.
- O3 `base_mod_defect` / `pr_mod_ok` (proved, concrete): with base behavior (k1 defined as mod x y) x=5,y=2 the idiv constraints are unsatisfiable; with the PR's quotient (k1 = 5 div 2, k2 = 5 mod 2) they hold. This corroborates the fix; it is not a counterexample against the PR head.

## Correspondence / assumptions
F* models the integer constraints on mathematical ints (x,y,k1,k2) mirroring the four pushed disjunctions with the y=0 disjunct false. Assumes SMT-LIB div/mod semantics (Euclidean, as in Z3 arith). Inherits only F* stdlib FStar.Math.Lemmas; no base Z3 modules imported; no admits/assumes.
Not mechanized: C++ execution, proof-term plumbing (mk_def_intro/apply_def/th_lemma premises), memory safety, caching (m_app2fresh) interactions.

## Exclusions (not covered)
Congruence th-lemma premise correctness (function 2) and 0^0 proof sort handling for int-typed power (function 3, p0 is a real var defined via power(int 0, int 0)); sin/cos basis changes and unit-circle th-lemma axiom; quantifier bind-proof/oeq change in process quantifier; push_cnstr_pr() zero-premise th-lemma; test additions in src/test/simplifier.cpp. These remain manually reviewed only.

## Reproduce
cd /tmp/gh-aw/agent/fstar-audit && see verification_log.