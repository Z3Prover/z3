# F* audit PR #11524 @ f6256d35 (partial scope)
Base f3df3153. Open at this head; prior audit comment is for ec09d65d only.

Source: fstar/Z3DagScope.fst @ head (sha256 372a38e6...77f8a), scope interning (~l.30-185).
Proved: (1) lemma_scope_canonical: equal scope_ids => equal ids; (2) lemma_push: push preserves scopes_ok, grows table, id denotes h :: scope_ids t (found and new-cell branches); (3) push work never increases (refinement type).

Mapping: definitions restated verbatim except CS.table_units := 1 (specialisation), T.phase local, and Z3ProofIndex.index_tree inlined with lemma_index_put re-proved (pinned fstar.exe rejects base module: custard_inline missing). No admit/assume. Only FStar stdlib trusted.

Excluded: walk, memo_ok, under/intern_scope, rest of Z3DagScope.fst, Z3DagGuard*, Z3Checked*, Z3Sorted*, Z3NameUnits*, Z3NnfReplayChecked, Cherry/Native/OCaml runtimes, tools, specs. No C++ execution/memory safety claims.

Reproduce: timeout 120 fstar.exe --smt .../z3-4.13.3/bin/z3 --z3version 4.13.3 --z3rlimit 10 --cache_dir cache --odir out Z3DagScopeInterning.fst (F* 2026.09.27, Z3 4.13.3, exit 0).
