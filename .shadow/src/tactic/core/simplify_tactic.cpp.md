# Shadow: src/tactic/core/simplify_tactic.cpp

**Language**: C++ | **Lines**: 134 | **Last modified**: 2026-01-14

## File-Level

_No discoveries yet._

## `class simplify_tactic`

### `simplify_tactic.m`

_No discoveries yet._

### `simplify_tactic.reset`

_No discoveries yet._

### `simplify_tactic.collect_statistics`

_No discoveries yet._

### `simplify_tactic.operator`

_No discoveries yet._

### `simplify_tactic.report`

_No discoveries yet._

### `simplify_tactic.new_curr`

_No discoveries yet._

### `simplify_tactic.new_pr`

_No discoveries yet._

### `simplify_tactic.get_num_steps`

_No discoveries yet._

### `simplify_tactic.updt_params`

_No discoveries yet._

### `simplify_tactic.get_param_descrs`

_No discoveries yet._

### `simplify_tactic.operator`

_No discoveries yet._

## `tactic_exception`

_No discoveries yet._

### `simplify_tactic.cleanup`

_No discoveries yet._

### `simplify_tactic.collect_statistics`

_No discoveries yet._

### `simplify_tactic.get_num_steps`

_No discoveries yet._

## `mk_simplify_tactic`

_No discoveries yet._

## `clean`

_No discoveries yet._

## `mk_elim_and_tactic`



- mk_elim_and_tactic implements the elim-and feature as a params_ref preset over mk_simplify_tactic via using_params, while get_param_descrs delegates to th_rewriter; new simplify variants can follow this wrapper pattern instead of duplicating the tactic implementation.
  _(verified, source: exploration, labels: [feature-gap])_
  Dream report: `_dreams/20260730-042945Z-c3-t03-simplify-tactic-preset-variant/`
## `using_params`

_No discoveries yet._

## Cross-References

_No cross-cutting discoveries yet._
