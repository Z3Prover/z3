# Shadow: src/solver/solver.cpp

**Language**: C++ | **Lines**: 352 | **Last modified**: 2025-02-10

## File-Level

_No discoveries yet._

### `solver.get_num_assertions`

_No discoveries yet._

### `solver.get_assertion`

_No discoveries yet._

### `solver.display`

_No discoveries yet._

## `fmls`

_No discoveries yet._

## `visitor`

_No discoveries yet._

### `solver.display_dimacs`

_No discoveries yet._

## `fmls`

_No discoveries yet._

### `solver.get_assertions`

_No discoveries yet._

### `solver.get_assertions`

_No discoveries yet._

## `result`

_No discoveries yet._

## `class scoped_assumption_push`

_No discoveries yet._

### `solver.get_consequences`

_No discoveries yet._

## `st`

_No discoveries yet._

## `get_consequences_core`

_No discoveries yet._

### `solver.get_consequences_core`

_No discoveries yet._

## `tmp`

_No discoveries yet._

## `asms1`

_No discoveries yet._

## `eval`

_No discoveries yet._

## `core`

_No discoveries yet._

## `_scoped_push`

_No discoveries yet._

## `_scoped_push`

_No discoveries yet._

### `solver.find_mutexes`

_No discoveries yet._

### `solver.preferred_sat`

_No discoveries yet._

## `check_sat`

_No discoveries yet._

## `is_m_atom`

_No discoveries yet._

### `solver.is_literal`

_No discoveries yet._

## `is_m_atom`

_No discoveries yet._

### `solver.assert_expr`

_No discoveries yet._

## `fml`

_No discoveries yet._

### `solver.assert_expr`

_No discoveries yet._

## `fml`

_No discoveries yet._

## `a`

_No discoveries yet._

### `solver.collect_param_descrs`

_No discoveries yet._

## `sp`

_No discoveries yet._

## `mp`

_No discoveries yet._

### `solver.display_parameters`

_No discoveries yet._

### `solver.reset_params`

_No discoveries yet._

## `sp`

_No discoveries yet._

### `solver.updt_params`

_No discoveries yet._

## `sp`

_No discoveries yet._

### `solver.get_units`

_No discoveries yet._

## `fmls`

_No discoveries yet._

### `solver.get_non_units`

_No discoveries yet._

## `result`

_No discoveries yet._

### `solver.check_sat`

_No discoveries yet._

## `_st`

_No discoveries yet._

### `solver.dump_state`

_No discoveries yet._

## `ous`

_No discoveries yet._


## `solver::get_consequences_core`

- solver::get_consequences_core performs an initial satisfiability check and then may issue one additional check_sat per candidate fixed variable, using temporary assumptions for Boolean constants and a scoped assertion for non-Boolean equalities.
  _(verified, source: exploration, labels: [performance])_
  Dream report: `_dreams/20260730-211723Z-c7-t06-solver-consequences-recheck-loop/`
## Cross-References

_No cross-cutting discoveries yet._
