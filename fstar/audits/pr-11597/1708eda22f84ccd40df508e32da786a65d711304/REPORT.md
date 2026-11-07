# F* audit of PR #11597 at 1708eda22f84ccd40df508e32da786a65d711304

Scope: PARTIAL. Selected function: `theory_datatype::get_seq_args` in src/smt/theory_datatype.cpp (head ~L1000-1035), with its call guards in `explain_is_child` (~L873) and `occurs_check_enter` (~L953). Three obligations. Excluded: test file src/test/parametric_datatype.cpp, occurs_check driver/stack/m_parent logic, finite-set/array paths, model construction, memory safety, enode mark handling, AST plumbing.

## Intended property
Every datatype-sorted term reachable through seq.unit / seq.++ nesting at any Seq depth (modulo equalities) is returned to the occurs check, so cycles through Seq(Seq T) give a conflict rather than reaching model construction.

## Model (Z3SeqArgsNested.fst)
Congruence classes are abstracted as a tree `sq` = Atom | Unit elem | Cat sq sq, with elem = datatype leaf (D n) | nested seq (S sq). `collect_head` models the PR (seq-sorted unit arg is re-queued via add_todo, i.e. recursed into). `collect_base` models the old code (seq-sorted unit arg pushed to m_args, later dropped by process_arg because it is not a datatype).

## Obligations
1. O1 PROVED: `mem n (collect_head s) == occurs s n` (sound and complete at any depth).
2. O2 PROVED: base collection is a subset of head collection (the PR only adds results).
3. O3 PROVED (witness of the old bug, not a counterexample to the PR): for t = node(unit(unit t)), base collector misses t while head collector finds it.

No counterexample to the PR found.

## Correspondence and assumptions
The model treats class-sibling iteration as a tree walk; the real code iterates equivalence classes (possibly cyclic) using root marks to terminate. Manually reviewed only: termination on cyclic seq classes, correctness of used_eqs justification pairs (n,sibling) for explain_is_child, and removal of the is_datatype(se) guard at the two call sites (now any seq, e.g. Seq Int, costing traversal but yielding no datatype leaves). Mark/unmark both use get_root() symmetrically. Not mechanized: C++ execution, explanation-clause soundness, sort tests. Only FStar.List.Tot is used; no base modules imported; no admit/assume.

## Reproduce
See verification_log.
