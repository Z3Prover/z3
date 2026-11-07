# F* audit of PR 11562 @ 6d75cefd3ff3f48f697b17a36080393fba25b46d (base 5bab8997)

fstar-nfv-audit:6d75cefd3ff3f48f697b17a36080393fba25b46d

Partial scope: one function, `context::internalize_quantifier` (+ `internalize_quantifier_polarity` guards, the NOT case of `internalize_formula`, `undo_mk_bool`), taken from the PR diff patch in `fstar-pr.json` (not full function bodies fetched).

## Obligations (all proved in `QuantPolarityHead6d75.fst`)
- O1: every polarity at which a quantifier atom may occur gets an NNF/Skolem clause (exists-pos, any-neg); forall-pos is covered by the quantifier manager.
- O1b: no clause emitted for an impossible polarity.
- O2: NOT in gate context flips the required polarity (`~polarity`), involutively.
- O3: manager registration at `mk_bool_var` and deletion in `undo_mk_bool` are both guarded by `is_forall`, so balanced and independent of first polarity.
- O4: seen-set idempotence and rollback on failure (modelled abstractly).
No counterexample found.

## Correspondence / assumptions
lbool and polarity guards modelled exactly; callers' polarity arguments are assumed correct (not verified). Default `l_undef` is treated as both polarities. NNF result correctness, proofs, backtracking trail, and relevancy are NOT modelled; they rely on base `Z3QuantifierNnf`/`Z3Skolemization` and manual review.

## Exclusions
All other changed files (smt_context.cpp, theory_*.cpp, seq_regex, model_finder, arith_eq_adapter, conflict resolution, tests, CI/pulse tooling, earlier audit artefacts). Not mechanized C++ execution or memory safety.

## Reproduce
fstar.exe --smt z3 --z3version 4.13.3 --include fstar --z3rlimit 10 --cache_dir cache --odir out QuantPolarityHead6d75.fst
