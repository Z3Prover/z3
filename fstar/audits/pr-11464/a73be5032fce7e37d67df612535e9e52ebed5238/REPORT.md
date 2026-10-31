# F* audit: PR #11464 @ a73be5032fce7e37d67df612535e9e52ebed5238 (base 30daf835d2c23b71298e83451ce03d7fa203376b)

Partial scope: only the new `next_case_split_core` in `src/smt/smt_case_split_queue.cpp` (shared by the activity-based `next_case_split` and the delayed-queue path) was modelled. Semantic source audit of a pure-queue abstraction, not mechanized C++ verification.

## Obligations (all proved)
1. Result is `null_bool_var` iff every queued var is assigned.
2. A returned var is unassigned and was in the queue (erase(next) is therefore valid).
3. If some unassigned relevant var is queued, the returned var is relevant (new guarantee); if the min is irrelevant, a relevant var is chosen, falling back to the min when none exists.
No counterexample found.

## Correspondence
`drop_assigned` = the while/erase_min loop; `best` = the loop over m_queue picking strictly-higher activity relevant unassigned var; `core` = the function. Heap ordering, `erase`, and activity ties (strict `>`) are abstracted: the queue is a list with head = min_value, which only affects which relevant var is chosen, not the proved properties.

## Assumptions
`assigned`/`relevant`/`activity` are fixed during the call (true: single-threaded, no propagation inside). Queue elements are valid bool_vars. Standard F* library (FStar.List.Tot) only; no base modules imported.

## Not audited
- `next_case_split` random branch: new `is_relevant(next)` check; random var may be >= queue-invariants/out-of-range only if num_b_internalized==0 (pre-existing division by zero risk, unchanged).
- Changes in src/smt/smt_model_checker.cpp, src/smt/theory_datatype.cpp, src/test/smt_context.cpp (excluded: bound of three functions).
- Behavioral/completeness concern (manual, not proved): choosing an irrelevant var when no relevant one remains preserves prior behavior; O(n) scan per decision may cost performance.
- Memory safety, queue iteration/erase semantics, whole-solver soundness.

## Reproduce
cd /tmp/gh-aw/agent/fstar-audit && /tmp/gh-aw/fstar/bin/fstar.exe --smt /tmp/gh-aw/fstar/lib/fstar/z3-4.13.3/bin/z3 --z3version 4.13.3 --include fstar --z3rlimit 10 --cache_dir cache --odir out CaseSplitAudit.fst
F* 2026.09.27; Z3 4.13.3 (pinned independent backend). Source sha256 64be2f875fa1979041d99a51fb3f7b971da2f6ce51c83375c8acf7d3fb8619bb