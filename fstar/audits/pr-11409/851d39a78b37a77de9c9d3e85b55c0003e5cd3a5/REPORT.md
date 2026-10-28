# F* audit of PR #11409 @ 851d39a78b37a77de9c9d3e85b55c0003e5cd3a5 (base 02f6a7e144ed5ce81ab07a1373fd667c60ead0c2)

Partial scope: one changed production function, `min_cut::augment_path` (`src/util/min_cut.cpp`, line 166). Excluded: `src/test/min_cut.cpp`, `src/test/main.cpp`, `src/test/CMakeLists.txt` (test-only, not audited; tests not executed), and all other min_cut functions (unchanged; augmenting-path selection, max-flow optimality, and cut extraction not modelled).

Source hashes (sha256 of decoded file): base `f1368329aa9f944b1206caf2e82513d0841e4dab3da4acbbe7a9c3abce947bbd`, head `224ae4f0fbef992d2e6776b254b376604a1b01239f6607c2abbe42249661ffc3`. The only source diff is `edge(1, max)` -> `edge(l, max)` at line 166.

Intended property: when augmenting along pred chain k -> l (l = m_pred[k]) by bottleneck m, the residual graph gets reverse capacity m on arc k->l; other arcs of m_edges[k] are unchanged.

Obligations (module `MinCutReverseArc`, models the adjacency list of node k, lines 157-167):
1. **Counterexample (base behaviour, checked):** with arc k->l absent, base creates k->1 instead, so cap(k->l)=0 after augmenting by m>0 (`cex_base`, `cex_path`). This confirms the bug fixed by the PR; it is a witness against the BASE, not the head.
2. **Proved (head):** `head_reverse`: if at most one arc k->l exists, afterwards cap(k->l) = old + m, in both the exists and missing branches.
3. **Proved (head):** `head_other`: capacity to any j != l is unchanged.

Assumptions/correspondence: `bump` mirrors the already_exists loop (adds m to all arcs to l; the proof assumes at most one such arc, which holds because add_edge-created parallel arcs may NOT satisfy it: parallel arcs to l would each get +m, which is pre-existing behaviour and unchanged by the PR). Naturals are unbounded, so unsigned overflow of `weight += max` is not modelled (manual review). Residual-graph soundness overall, termination, memory safety and C++ execution are not mechanized. Standard F* library and Z3 4.13.3 are trusted; no admit/assume.

Note: a subtle side-effect: in the head, a self-loop-free requirement l != k is assumed (pred chain acyclic).

Reproduce:
`/tmp/gh-aw/fstar/bin/fstar.exe --smt /tmp/gh-aw/fstar/lib/fstar/z3-4.13.3/bin/z3 --z3version 4.13.3 --z3rlimit 10 --include fstar --cache_dir cache --odir out MinCutReverseArc.fst` (F* 2026.09.27, Z3 4.13.3). Result: exit 0, all VCs discharged.
