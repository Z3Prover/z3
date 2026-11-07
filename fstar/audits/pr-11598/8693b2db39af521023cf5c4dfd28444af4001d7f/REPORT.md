## F* audit of PR 11598 @ 8693b2db

**Changed code**: src/smt/theory_datatype.cpp (blob SHA 819dd40b...-decoded file sha256 819dd40ba40e8edf0e0a673cc220628fcf54ce3b1c7632e4a5299b4340f698f2), lines 1242-1245 of merge_eh at head: range-for over d2->m_subterms replaced by indexed loop re-reading size(). Base SHA d86b80e7.

**Bug being fixed**: add_subterm_predicate(v1,e) can call propagate_subterm -> force_push/propagation, which may call add_subterm_predicate on another var whose find() is still d2 (union-find not yet updated), push_back-ing to d2->m_subterms and invalidating range-for iterators.

### Obligation 1 (proved)
For any append-only oracle (length bounded by b) modelling propagation in each add_subterm_predicate call, the indexed loop terminates and the final d1 contains every element of the final d2 (covers d1 d2 (length d2)); d2 final extends the initial d2 as a prefix.

### Mapping to C++
list nat = ptr_vector(enode) m_subterms; add = contains()+push_back; oracle = side effects of propagation on d2; loop = lines 1243-1245.

### Assumptions (not proven)
- Propagation only appends to d2->m_subterms (trail restore_vector pops only on backtrack, not during the loop); growth is finitely bounded.
- v1 != v2 roots, so d1 and d2 are distinct vectors; push_back on d1 does not move d2 storage.
- Standard FStar.List.Tot library and F* trusted core.

### Not covered / excluded
memory safety, actual C++ execution, whether other loops (e.g., recognizer loop at 1238, propagate_subterm_with_constructor, which copies the vector) have similar hazards, the regression test test_subterm_merge, and the soundness of subterm propagation itself. The model is a semantic abstraction, not mechanized verification of C++.

### Reproduce
See verification_log; run fstar.exe with --smt (pinned z3 4.13.3) --z3version 4.13.3 --z3rlimit 10 on SubtermMergeAudit.fst.