# Shadow: src/ast/euf/euf_egraph.cpp

**Language**: C++ | **Lines**: 1120 | **Last modified**: 2026-01-14

## File-Level

_No discoveries yet._

## `Bjorner`

_No discoveries yet._

### `egraph.mk_enode`

_No discoveries yet._

### `egraph.find`

_No discoveries yet._

### `egraph.insert_table`

_No discoveries yet._

### `egraph.erase_from_table`

_No discoveries yet._

### `egraph.reinsert_equality`

_No discoveries yet._

### `egraph.queue_literal`

_No discoveries yet._

### `egraph.force_push`

_No discoveries yet._

### `egraph.update_children`

_No discoveries yet._

### `egraph.mk`

_No discoveries yet._

### `egraph.add_plugin`

_No discoveries yet._

### `egraph.propagate_plugins`

_No discoveries yet._

### `egraph.add_th_eq`

_No discoveries yet._

### `egraph.add_th_diseq`

_No discoveries yet._

### `egraph.add_literal`

_No discoveries yet._

### `egraph.new_diseq`

_No discoveries yet._

### `egraph.new_diseq`

_No discoveries yet._

### `egraph.add_th_diseqs`

_No discoveries yet._

### `egraph.set_th_propagates_diseqs`

_No discoveries yet._

### `egraph.th_propagates_diseqs`

_No discoveries yet._

### `egraph.add_th_var`

_No discoveries yet._

### `egraph.register_shared`

_No discoveries yet._

### `egraph.undo_add_th_var`

_No discoveries yet._

### `egraph.set_merge_tf_enabled`

_No discoveries yet._

### `egraph.set_cgc_enabled`

_No discoveries yet._

### `egraph.set_relevant`

_No discoveries yet._

### `egraph.toggle_cgc_enabled`

_No discoveries yet._

### `egraph.set_value`

_No discoveries yet._

### `egraph.set_lbl_hash`

_No discoveries yet._

### `egraph.pop`

_No discoveries yet._

### `egraph.merge`

_No discoveries yet._

### `egraph.remove_parents`

_No discoveries yet._

### `egraph.reinsert_parents`

_No discoveries yet._

### `egraph.merge_th_eq`

_No discoveries yet._

### `egraph.undo_eq`

_No discoveries yet._

### `egraph.propagate`

_No discoveries yet._

### `egraph.set_conflict`

_No discoveries yet._

### `egraph.merge_justification`

_No discoveries yet._

### `egraph.unmerge_justification`

_No discoveries yet._

### `egraph.are_diseq`

_No discoveries yet._

### `egraph.get_enode_eq_to`

_No discoveries yet._

## `find`

_No discoveries yet._

### `egraph.tmp_eq`

_No discoveries yet._

### `egraph.push_congruence`

_No discoveries yet._

### `egraph.find_lca`

_No discoveries yet._

### `egraph.push_to_lca`

_No discoveries yet._

### `egraph.push_lca`

_No discoveries yet._

### `egraph.push_todo`

_No discoveries yet._

### `egraph.begin_explain`

_No discoveries yet._

### `egraph.end_explain`

_No discoveries yet._

### `egraph.explain`

_No discoveries yet._

### `egraph.explain_eq`

_No discoveries yet._

### `egraph.explain_eq`

_No discoveries yet._

### `egraph.explain_diseq`

_No discoveries yet._

### `egraph.explain_todo`

_No discoveries yet._

### `egraph.invariant`

_No discoveries yet._

### `egraph.display`

_No discoveries yet._

### `egraph.display`

_No discoveries yet._

### `egraph.collect_statistics`

_No discoveries yet._

### `egraph.copy_from`

_No discoveries yet._

## `tr`

_No discoveries yet._


## `egraph::force_push`

- euf::egraph defers scope materialization in m_num_scopes until force_push(), which records the update limit, pushes the region scope, records the theory-equality qhead, and notifies plugins in one batch.
  _(verified, source: exploration)_
  Dream report: `_dreams/20260730-202703Z-c5-t04-euf-force-push-deferred-scopes/`
## Cross-References

_No cross-cutting discoveries yet._
