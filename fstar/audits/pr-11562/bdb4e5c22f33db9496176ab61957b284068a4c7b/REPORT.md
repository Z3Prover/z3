# F* audit of PR 11562 at bdb4e5c22f33db9496176ab61957b284068a4c7b (base 5bab89972dc48c2d5560b1e6e0df8297bd85e2ea)

Scope: PARTIAL. Selected function: `context::internalize_quantifier` / `internalize_quantifier_polarity` (src/smt/smt_internalizer.cpp, patch hunk @@ -649,25 +652,73), plus the polarity propagation in `internalize_formula` (NOT gate: `~polarity`). Source was read from the GitHub PR files patch for the head SHA (not full function bodies; patch excerpts only).

## Obligations (module QuantPolarityHeadBdb4.fst)
1. O1 (proved): for kind in {forall, exists} and any lbool polarity, every polarity permitted by the argument is covered: positive forall by quantifier-manager registration, positive exists by pos clause (polarity != l_false), negative of either by neg clause (polarity != l_true).
2. O2 (proved): NOT-gate shortcut `~polarity` preserves the permitted-occurrence set under negation.
3. O3 (proved): clause (~premise \/ result) with premise = literal(var(q), !positive) is source ==> result for source = q or not q.

## Correspondence and assumptions
`lb` models lbool, `kind` models is_forall/is_exists; guards copy `is_exists(q) && polarity != l_false` and `polarity != l_true`. Assumed (manually reviewed, not proved): nnf produces a result equivalent/equisatisfiable per its own proof, the `seen` sets and trail undo behave as intended, relevancy watch correctness, proof-term construction, backtracking via undo_mk_bool (`is_forall` guard on m_qmanager->del), and that callers pass sound polarity (gate children use default l_undef, which is conservative). Only base Prelude/standard F* libraries are used.

## Exclusions
All other changed functions/files: smt_context.cpp polarity arguments, internalize_formula enode creation for quantifiers, cached_generation change, assign_quantifier false-case change, theory files, tests, workflows, fstar/tools. No C++ execution, memory safety, or whole-solver claims. No counterexample was sought beyond guard analysis; none found in the abstraction.

## Reproduce
timeout 120 /tmp/gh-aw/fstar/bin/fstar.exe --smt /tmp/gh-aw/fstar/lib/fstar/z3-4.13.3/bin/z3 --z3version 4.13.3 --include fstar --z3rlimit 10 --cache_dir cache --odir out QuantPolarityHeadBdb4.fst
F* 2026.09.27, Z3 4.13.3. File sha256 6956581c0d8fd55129252b022497b90facf8e78be54a189e9019366351cb5dcc.
