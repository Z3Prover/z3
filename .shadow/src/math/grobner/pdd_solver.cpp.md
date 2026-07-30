# Shadow: src/math/grobner/pdd_solver.cpp

**Language**: C++ | **Lines**: 570 | **Last modified**: 2025-06-04

## File-Level

_No discoveries yet._

## `Bjorner`

_No discoveries yet._

## `Nachmanson`

_No discoveries yet._

### `solver.adjust_cfg`

_No discoveries yet._

### `solver.saturate`

_No discoveries yet._

### `solver.simplify`

_No discoveries yet._

## `s`

_No discoveries yet._

### `solver.superpose`

_No discoveries yet._

### `solver.simplify_using`

_No discoveries yet._

### `solver.well_formed`

_No discoveries yet._

### `solver.simplify_using`

_No discoveries yet._

## `sr`

_No discoveries yet._

### `solver.simplify_using`

_No discoveries yet._

## `try_simplify_using`

_No discoveries yet._

### `solver.try_simplify_using`

_No discoveries yet._

### `solver.simplify_using`

_No discoveries yet._

### `solver.superpose`

_No discoveries yet._

## `r`

_No discoveries yet._

### `solver.step`

_No discoveries yet._

## `sd`

_No discoveries yet._

### `solver.init_saturate`

_No discoveries yet._

### `solver.pick_next`

_No discoveries yet._

### `solver.reset`

_No discoveries yet._

### `solver.add`

_No discoveries yet._

### `solver.add_subst`

_No discoveries yet._

### `solver.simplify`

_No discoveries yet._

### `solver.canceled`

_No discoveries yet._

### `solver.done`

_No discoveries yet._

### `solver.get_queue`

_No discoveries yet._

### `solver.del_equation`

_No discoveries yet._

### `solver.retire`

_No discoveries yet._

### `solver.pop_equation`

_No discoveries yet._

### `solver.push_equation`

_No discoveries yet._

### `solver.update_stats_max_degree_and_size`

_No discoveries yet._

### `solver.collect_statistics`

_No discoveries yet._

### `solver.display`

_No discoveries yet._

### `solver.display`

_No discoveries yet._

## `display_statistics`

_No discoveries yet._

### `solver.display_statistics`

_No discoveries yet._

### `solver.invariant`

_No discoveries yet._


## `solver::try_simplify_using`

- math::grobner::pdd_solver increments the simplified-attempt statistic before knowing whether reduction changes the target, and a too-complex reduction sets m_too_complex then returns false without updating the equation.
  _(verified, source: exploration, labels: [tech-debt])_
  Dream report: `_dreams/20260730-213035Z-c8-t03-pdd-solver-too-complex-bailout/`
## Cross-References

_No cross-cutting discoveries yet._
