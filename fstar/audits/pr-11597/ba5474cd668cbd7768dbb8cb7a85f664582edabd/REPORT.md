# F* audit PR 11597 @ ba5474cd668cbd7768dbb8cb7a85f664582edabd (base d86b80e7)

Partial scope: ONE changed function, get_nested_args (src/smt/theory_datatype.cpp ~L940-1000) with helper has_nested_datatype (~L925-937) and caller guards (process_arg ~L905-922; explain_is_child ~L841-858). Three obligations on an abstract model.

## Obligations
- O1 (proved): has_nested_datatype(s) == datatype occurs under a chain of array-range / seq / finite-set element sorts.
- O2 (proved): the add_todo sort filter drops no datatype leaf, assuming sort-typing well-formedness (a container whose sort has no nested datatype has no datatype descendants via select/default/unit/union/member edges).
- O3 (proved): the root-keyed visited guard keeps the worklist duplicate-free and every worklist element visited, so each container class is expanded once (termination on cyclic classes).
- Witness (checked, positive): array(seq(DT)) -> seq(DT) -> DT leaf is found; the base guard is_datatype(array range) would not traverse Seq DT. Confirms mixed-depth fix; not a counterexample.

## Mapping / assumptions
srt models sorts; node models the quotiented enode graph (Leaf = datatype enode in m_args, Node = container class). Cycles quotiented to trees; congruence closure, parent lists, is_in literal assignment and array default internalization are abstracted. Assumption: wf (sort typing). Only FStar.List.Tot and FStar.Classical used; no admit/assume/axioms; no base fstar/ modules imported. Sources: theory_datatype.cpp head sha256 244b0a0a2ccbdada88a3c6132e30a72d5493153c2a8b84e98550f097aecbe839; base d86b80e7 sha256 dc1a6972981e8d5edbe289da0169a4970250f8f9185cea1fe06a4fef3dc4f9b1.

## Excluded / manually reviewed (not mechanized)
- Soundness/completeness of conflict explanation (m_used_eqs/m_used_lits): select parents, is_in literals assigned true, equalities n=sibling. VERIFY(found) in explain_is_child relies on recomputation matching the earlier traversal; array default internalization (ctx.internalize inside get_nested_args, also reached during explanation) is a side effect deserving manual review, as is the m.inc() early break returning partial results (only when used_eqs is null).
- src/ast/datatype_decl_plugin.cpp covariance validation, theory_datatype.h, tests, m_used_lits reset.
- C++ execution, memory safety, array theory interaction, outer DFS termination.

Reproduce: see verification.log.
