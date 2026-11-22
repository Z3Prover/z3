# F* audit PR #11691 @ 77c4b8194142d38839906ee5b3264a7223658f9c (base 708879ef23599153d4f0adb3af58fb514e2c8942)

Scope: 1 changed function, `theory_datatype::get_nested_args` (src/smt/theory_datatype.cpp, lines 940-1002 at head; the `add_todo` lambda, lines 948-955). The test file change (src/test/parametric_datatype.cpp) is excluded: tests are not proof targets.
Source SHA-256: head 58d584125667be390ad6b9ed96f93fde9d620876024a027531d323773d43de14, base 9bed24d8ebfeec03d4ed61514f99f94cbf9d266a71c7b9cd2e5956e54679564a. The whole diff is the two lines at 950-951.

## Obligations (all proved)
- O1 (refutes the BASE guard, shows the fix is needed): with the old always-true test, re-expanding a class that contains a concat over itself appends to `todo` every time (`o1_old_unbounded`: length = k+1 for k re-expansions), i.e. unbounded growth. This confirms the PR's stated problem. It is a pre-existing defect, not a counterexample to the PR.
- O2 (new guard preserves invariant): `todo` has no duplicates and `visited` = set of `todo` (`o2_new_preserves_inv`); the self-loop case yields `todo == [r]` for any number of re-expansions (`o2_self_bounded`).
- O3 (no class lost): after `add_new r`, r is in `todo`, and nothing previously queued is dropped (`o3_complete`), so skipping only removes repeat visits.

## Correspondence
`root` classes <-> `n->get_root()`; `visited` <-> `obj_hashtable<enode>`; `add_new` <-> `!visited.contains(r)` then `visited.insert(r)` then `todo.push_back(n)`. Only the container branch is modelled; the datatype branch (`m_args.push_back`) is unchanged by the PR.

## Assumptions / not mechanized
- `contains`/`insert` of obj_hashtable behave as set membership/insert (manually reviewed; hashtable.h).
- Modelled as the root only; the PR pushes `n` (not the root) to `todo`, as before. Visiting the first representative of a class is sufficient because the loop iterates all siblings of `n` (`for sibling : *n` covers the whole class) and the array/finite-set branches use `n->get_root()`'s parents.
- Manually reviewed, not modelled: explanation collection (`used_eqs`/`used_lits`) now only records equalities for the first-visited member of each class. Because explain_is_child calls get_nested_args again per constructor argument and checks `aarg->get_root() == child->get_root()`, a second node of an already-visited class reached via a different path no longer contributes its own `n != sibling` equalities. Since all equalities within a class are connected via the e-graph's own explanation (enode_pair(aarg, child) is pushed), this appears sound but is not proved here; worth a reviewer's eye.
- Not covered: C++ execution, memory safety, e-graph invariants, termination of the outer loop beyond this guard, the whole solver.
- Base modules inherited: none imported (`--include fstar` provided but unused); only FStar.List.Tot and FStar.Classical from the standard library.

## Reproduce
See verification_log. Tools: F* 2026.09.27, Z3 4.13.3 (pinned release).
