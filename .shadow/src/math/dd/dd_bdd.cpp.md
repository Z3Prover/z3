# Shadow: src/math/dd/dd_bdd.cpp

**Language**: C++ | **Lines**: 1253 | **Last modified**: 2025-05-28

## File-Level

_No discoveries yet._

## `Bjorner`

_No discoveries yet._

### `bdd_manager.apply_const`

_No discoveries yet._

### `bdd_manager.apply`

_No discoveries yet._

## `_sp`

_No discoveries yet._

## `apply_rec`

_No discoveries yet._

### `bdd_manager.mk_true`

_No discoveries yet._

### `bdd_manager.mk_false`

_No discoveries yet._

### `bdd_manager.mk_and`

_No discoveries yet._

### `bdd_manager.mk_or`

_No discoveries yet._

### `bdd_manager.mk_xor`

_No discoveries yet._

### `bdd_manager.mk_exists`

_No discoveries yet._

### `bdd_manager.mk_forall`

_No discoveries yet._

### `bdd_manager.check_result`

_No discoveries yet._

### `bdd_manager.apply_rec`

_No discoveries yet._

### `bdd_manager.push`

_No discoveries yet._

### `bdd_manager.pop`

_No discoveries yet._

### `bdd_manager.read`

_No discoveries yet._

### `bdd_manager.pop_entry`

_No discoveries yet._

### `bdd_manager.push_entry`

_No discoveries yet._

### `bdd_manager.make_node`

_No discoveries yet._

## `n`

_No discoveries yet._

## `mem_out`

_No discoveries yet._

### `bdd_manager.try_cnf_reorder`

_No discoveries yet._

### `bdd_manager.try_reorder`

_No discoveries yet._

### `bdd_manager.current_cost`

_No discoveries yet._

## `cnf_size`

_No discoveries yet._

## `dnf_size`

_No discoveries yet._

### `bdd_manager.is_bad_cost`

_No discoveries yet._

### `bdd_manager.sift_var`

_No discoveries yet._

### `bdd_manager.sift_up`

_No discoveries yet._

### `bdd_manager.init_reorder`

_No discoveries yet._

### `bdd_manager.reorder_incref`

_No discoveries yet._

### `bdd_manager.reorder_decref`

_No discoveries yet._

### `bdd_manager.reserve_var`

_No discoveries yet._

### `bdd_manager.mk_var`

_No discoveries yet._

## `bdd`

_No discoveries yet._

### `bdd_manager.mk_nvar`

_No discoveries yet._

## `bdd`

_No discoveries yet._

### `bdd_manager.mk_not`

_No discoveries yet._

## `_sp`

_No discoveries yet._

## `bdd`

_No discoveries yet._

### `bdd_manager.mk_not_rec`

_No discoveries yet._

### `bdd_manager.mk_cofactor`

_No discoveries yet._

## `_sp`

_No discoveries yet._

## `bdd`

_No discoveries yet._

### `bdd_manager.mk_cofactor_rec`

_No discoveries yet._

## `is_true`

_No discoveries yet._

## `mk_cofactor_rec`

_No discoveries yet._

## `mk_cofactor_rec`

_No discoveries yet._

### `bdd_manager.mk_ite`

_No discoveries yet._

## `_sp`

_No discoveries yet._

## `bdd`

_No discoveries yet._

### `bdd_manager.mk_ite_rec`

_No discoveries yet._

### `bdd_manager.mk_exists`

_No discoveries yet._

## `bdd`

_No discoveries yet._

### `bdd_manager.mk_forall`

_No discoveries yet._

## `bdd`

_No discoveries yet._

### `bdd_manager.mk_quant`

_No discoveries yet._

### `bdd_manager.mk_quant_rec`

_No discoveries yet._

### `bdd_manager.count`

_No discoveries yet._

### `bdd_manager.bdd_size`

_No discoveries yet._

### `bdd_manager.alloc_free_nodes`

_No discoveries yet._

### `bdd_manager.gc`

_No discoveries yet._

## `reachable`

_No discoveries yet._

### `bdd_manager.init_mark`

_No discoveries yet._

### `bdd_manager.display`

_No discoveries yet._

### `bdd_manager.well_formed`

_No discoveries yet._

### `bdd_manager.display`

_No discoveries yet._

### `bdd_manager.mk_eq`

_No discoveries yet._

### `bdd_manager.mk_eq`

_No discoveries yet._

### `bdd_manager.mk_eq`

_No discoveries yet._

### `bdd_manager.mk_ule`

_No discoveries yet._

### `bdd_manager.mk_uge`

_No discoveries yet._

### `bdd_manager.mk_ult`

_No discoveries yet._

### `bdd_manager.mk_ugt`

_No discoveries yet._

### `bdd_manager.mk_sle`

_No discoveries yet._

### `bdd_manager.mk_sge`

_No discoveries yet._

### `bdd_manager.mk_slt`

_No discoveries yet._

### `bdd_manager.mk_sgt`

_No discoveries yet._

### `bdd_manager.mk_add`

_No discoveries yet._

## `result`

_No discoveries yet._

### `bdd_manager.mk_add`

_No discoveries yet._

## `result`

_No discoveries yet._

### `bdd_manager.mk_sub`

_No discoveries yet._

## `result`

_No discoveries yet._

### `bdd_manager.mk_usub`

_No discoveries yet._

## `result`

_No discoveries yet._

### `bdd_manager.mk_usub`

_No discoveries yet._

### `bdd_manager.mk_mul`

_No discoveries yet._

## `mk_false`

_No discoveries yet._

### `bdd_manager.mk_mul`

_No discoveries yet._

## `mk_mul`

_No discoveries yet._

### `bdd_manager.mk_mul`

_No discoveries yet._

## `mk_usub`

_No discoveries yet._

## `mk_false`

_No discoveries yet._

### `bdd_manager.mk_concat`

_No discoveries yet._

### `bdd_manager.mk_quot_rem`

_No discoveries yet._

### `bdd_manager.mk_num`

_No discoveries yet._

## `result`

_No discoveries yet._

### `bdd_manager.mk_ones`

_No discoveries yet._

## `result`

_No discoveries yet._

### `bdd_manager.mk_zero`

_No discoveries yet._

## `result`

_No discoveries yet._

### `bdd_manager.mk_var`

_No discoveries yet._

## `result`

_No discoveries yet._

### `bdd_manager.mk_var`

_No discoveries yet._

## `mk_var`

_No discoveries yet._

### `bdd_manager.is_constv`

_No discoveries yet._

### `bdd_manager.to_val`

_No discoveries yet._

### `bddv.shl`

_No discoveries yet._

### `bddv.shr`

_No discoveries yet._

### `bddv.all0`

_No discoveries yet._

### `bddv.all1`

_No discoveries yet._


## `bdd_manager::apply`

- dd::bdd_manager::apply retries a mem_out failure exactly once after try_reorder(); a second mem_out is rethrown, so reordering is a single recovery attempt rather than an unbounded retry loop.
  _(verified, source: exploration, labels: [performance])_
  Dream report: `_dreams/20260730-200330Z-c4-t05-dd-bdd-memout-reorder/`
## Cross-References

_No cross-cutting discoveries yet._
