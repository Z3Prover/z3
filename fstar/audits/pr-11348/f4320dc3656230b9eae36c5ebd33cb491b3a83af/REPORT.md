# F* audit, PR #11348 @ f4320dc3656230b9eae36c5ebd33cb491b3a83af (base aa71a62f)

PR open at this SHA; no prior fstar-nfv-audit marker for this SHA.

## Changed behavior examined
1. src/smt/theory_arith_core.h (~L63-69): `ctx.assign(lit, nullptr)` becomes `mk_th_axiom(get_id(), lit)` when `m.proofs_enabled()`; otherwise unchanged.
2. src/smt/theory_lra.cpp (~L328-334): same replacement guarded by `proofs_enabled()`.
3. src/smt/theory_lra.cpp (~L1302-1308, power0 underspecified case): same replacement.
4. src/cmd_context/basic_cmds.cpp (~L523-528): `to_bool(value)` evaluated before `check_not_initialized`; only changes which error is reported first when both fail. Plausibly benign.

## Obligations
- O1 (intended): with proofs enabled the asserted literal has a proof justification (theory axiom) instead of an unjustified assignment; with proofs disabled behavior is identical. Status: INCONCLUSIVE. Branch guard is syntactically clear and the non-proof path is unchanged by inspection, but proving it in F* would require modeling mk_th_axiom's clause/proof-hint generation and that the resulting axiom is accepted by the proof checker for the theory (arith/lra), which is not in the trusted base. A model of just the guard would be tautological, so none was published.
- O2: The literal (eq e n) / (p = power0(x,y)) is actually valid in the theory (so a th_axiom is sound). Status: INCONCLUSIVE; requires semantics of the underspecified-term definitions (division/mod/power0 by zero) not formalized here; a checker-acceptance question for the arith theory-lemma hint is manually unreviewed.
- O3: basic_cmds reorder preserves successful-path behavior. Status: not mechanized; reviewed by inspection only (pure to_bool, no side effects before the check).

## Exclusions
All fstar/*.fst proof modules and tools changed in the PR (Z3ArrayEquality, Z3IntegerDivision, Z3NativeProof, Z3SortedProof, Z3TheoryNormalize, etc.), fstar/cherry_runtime/tests.cpp, tools scripts, prior audit directories, and OCAML_CHECKER_REPORT.md were not audited; PR proof modules were not imported as premises.

## Not covered
Memory safety, C++ execution semantics, proof-checker acceptance, and whole-solver soundness.

No F* invocations were run; no proof tooling output exists.