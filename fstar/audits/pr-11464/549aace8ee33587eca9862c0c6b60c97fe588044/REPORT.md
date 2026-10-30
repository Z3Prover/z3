# F* audit PR 11464 @ 549aace8ee33587eca9862c0c6b60c97fe588044
Base: 30daf835d2c23b71298e83451ce03d7fa203376b. Source: src/smt/smt_case_split_queue.cpp, hunk at new lines ~120-140 (next_case_split_core), called from next_case_split and the delayed variant.

## Obligations (all proved)
1. Returns null_bool_var iff the queue has no unassigned var; otherwise returns a queued, unassigned var.
2. If any unassigned relevant var is queued, the returned var is relevant (fixes irrelevant-first selection).
3. On an activity-ordered queue, a returned relevant var has maximal activity among unassigned relevant queued vars (strict > scan).

## Correspondence
Queue is a list in heap-min order (head = min_value, highest activity); drop_assigned = first while loop; best = for-loop over m_queue; core = branch on is_relevant(min). Falls back to the min when no relevant var exists (progress preserved). m_queue.erase(next) is not modelled beyond choice.

## Assumptions
m_queue iteration visits exactly the queued vars; heap ordering (sorted) holds for obligation 3; get_assignment/is_relevant/get_activity are pure and stable during the call. Base: F* standard library only.

## Exclusions (not audited)
random-split change in next_case_split (added is_relevant guard: falls through to core, no soundness issue noted); smt_model_checker.cpp re-internalize of popped quantifier; theory_datatype.cpp set_true_first_flag for non-rec constructor recognizers; src/test/smt_context.cpp tests; interaction of erase with heap invariants; memory safety. Phase-selection heuristics are not soundness-relevant to the model. Not a mechanized proof of C++ execution.

## Reproduce
fstar.exe --smt /tmp/gh-aw/fstar/lib/fstar/z3-4.13.3/bin/z3 --z3version 4.13.3 --z3rlimit 10 --cache_dir c --odir o CaseSplitCore.fst
F* 2026.09.27, Z3 4.13.3. Source sha256 of the module: see manifest.
