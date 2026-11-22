# F* NFV audit, PR 11699, head dbb1590a (base 1a1d88dd)

## Scope
Changed function: horn_tactic::operator() (horn_tactic.cpp ~404-410): the base early-return `if (in->proofs_enabled()) { result.push_back(in.get()); return; }` is deleted. Sources fetched via contents API at both SHAs; sha256 head file 2d77af031fbf3e5b2f299d13dc5024cef9396e5cc4cff8a39d71942035d92e8e, base f911db80c11d1a0fb1d5727c4c55b61b95f4eb278bcfc27f35cc06c9aed1b182 (decoded content). Only diff in that file is the 4 deleted lines.

## Obligations
- O1 (proved): without proofs, behavior unchanged; with proofs, dispatch changes from PassThrough to imp::operator() (simplify or verify). Lemmas o1_unchanged_without_proofs, o1_changed_with_proofs.
- O2 (inconclusive): with proofs enabled, simplify() resets the goal and re-asserts rule-derived formulas via goal::assert_expr(f), which attaches mk_asserted(f) (goal.cpp 266-267), and pc is not replaced by a Datalog proof. The F* lemma only shows the model distinction (transformed formulas are fresh leaves rather than inputs); it is NOT a checked witness that a wrong proof is produced, since whether asserted leaves are acceptable for horn-simplify is a design question the model cannot decide. Needs manual review.
- O3 (proved, dispatch only): verify() with proofs, monotone context and reachable answer asserts get_fact(proof) with proof2proof_converter; non-monotone leaves goal unchanged. Correctness of m_ctx.get_proof() is not modeled.

## Also noted (manual, not mechanized)
src/test/smt_context.cpp adds "horn" to the list of tactics expected to REJECT in proof mode (check_proof_mode_guards), yet the PR removes the guard and the shown operator() has no throw; whether another path rejects was not established here. The PR is marked WIP. A prior audit of head 534dea5 modeled a different (throwing) guard; it does not apply to this head.

## Correspondence and trust
F* models branch dispatch only (booleans is_simplify, proofs). Not mechanized: C++ execution, exception-to-unknown plumbing, proof object validity, memory safety, rest of the solver. Assumes F* 2026.09.27 and Z3 4.13.3 from pinned release; no base modules imported beyond the standard library; no admits/assumes.

## Exclusions
Only one non-test function changed; test changes in smt_context.cpp (list edit, blank line) not formalized.

## Reproduce
`/tmp/gh-aw/fstar/bin/fstar.exe --smt /tmp/gh-aw/fstar/lib/fstar/z3-4.13.3/bin/z3 --z3version 4.13.3 --include fstar --cache_dir cache --odir out --z3rlimit 10 HornProofRemoval.fst`