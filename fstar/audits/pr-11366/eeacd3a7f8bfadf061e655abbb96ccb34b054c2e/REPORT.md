## Scope
Changed function audited: `vacuous` (with the `block_parts` refactor it depends on and the `lemma_vacuous_sound` dispatch in `lemma_check_sound`). Excluded: PROOF_CHECKING.md, OCAML_CHECKER_REPORT.md, tools/test_native_bridge.ml, tools/test_native_checker.py (docs/tests, not audited); the rest of Z3Skolemization.fst is unchanged. The PR does not touch src/ C++.

## Obligations
1. **Proved**: PR head Z3Skolemization.fst (incl. `lemma_vacuous_sound`, which states observations_agree under the same hypotheses as `lemma_check_sound`) verifies in F* with the base dependencies, no admit/assume.
2. **Proved (concrete)**: `exists a:Int. false ~ false` (the z3test 4013 step) is accepted by a mirror of `vacuous`; a used-variable block `exists b:Bool. #0` is rejected against both `#0` and `false`.
3. **Proved (general)**: for empty witnesses, `substitute depth count [] [] e` succeeds iff no Var with index in [depth, depth+count) occurs in `e` (`subst_no_occ`, `no_occ_subst`), so `vacuous` is exactly the unused-block check the PR claims.

## Correspondence/assumptions
The audit module `Z3SkolemVacuousAudit` mirrors `block_parts`/`vacuous` (copied) and reuses base `substitute`, `source`, `instantiation`. Obligation 1 was checked on the actual head file. Inherited base assumptions: existing Z3QuantifierNnf.quantifier_model / Z3QuantifierPull.sample_values and F* standard library; hypotheses boolean_model, not_sound, quant_extensional. Not mechanized: the OCaml/Cherry extraction, the proof-term plumbing, C++ producers, memory safety. The --sorted-core path and constant-folded shapes remain out of scope (as PR states). No counterexample found; no witness search beyond the above.

## Reproduce
Copy base fstar/*.fst to a dir, replace Z3Skolemization.fst with head version, add Z3SkolemVacuousAudit.fst, run: fstar.exe --smt /tmp/gh-aw/fstar/lib/fstar/z3-4.13.3/bin/z3 --z3version 4.13.3 --z3rlimit 10 --include . --cache_dir C --odir O (file).fst