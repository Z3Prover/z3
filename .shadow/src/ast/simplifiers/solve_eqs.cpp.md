# Shadow: src/ast/simplifiers/solve_eqs.cpp

**Language**: C++ | **Lines**: 376 | **Last modified**: 2026-06-22

## File-Level

_No discoveries yet._

## `Bjorner`

_No discoveries yet._

### `solve_eqs.get_eqs`

_No discoveries yet._

### `solve_eqs.extract_dep_graph`

_No discoveries yet._

### `solve_eqs.extract_subst`

_No discoveries yet._

### `solve_eqs.normalize`

_No discoveries yet._

### `solve_eqs.apply_subst`

_No discoveries yet._

## `new_pr`

_No discoveries yet._

## `tmp`

_No discoveries yet._

### `solve_eqs.reduce`

_No discoveries yet._

## `context_solve`

_No discoveries yet._

### `solve_eqs.collect_num_occs`

_No discoveries yet._

### `solve_eqs.collect_num_occs`

_No discoveries yet._

### `solve_eqs.check_occs`

_No discoveries yet._

### `solve_eqs.is_linear`

_No discoveries yet._

### `solve_eqs.save_subst`

_No discoveries yet._

### `solve_eqs.filter_unsafe_vars`

_No discoveries yet._

## `rec`

_No discoveries yet._

### `solve_eqs.updt_params`

_No discoveries yet._

## `tp`

_No discoveries yet._

## `sp`

_No discoveries yet._

### `solve_eqs.collect_param_descrs`

_No discoveries yet._

### `solve_eqs.collect_statistics`

_No discoveries yet._


## `solve_eqs::extract_subst`

- solve_eqs::extract_subst silently abandons substitution extraction if the unsigned level budget would underflow, before inserting any remaining substitutions for that connected component.
  _(verified, source: exploration, labels: [feature-gap])_
  Dream report: `_dreams/20260730-204557Z-c6-t03-solve-eqs-level-overflow-guard/`
## Cross-References

_No cross-cutting discoveries yet._
