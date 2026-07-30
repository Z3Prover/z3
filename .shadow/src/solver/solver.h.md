# Shadow: src/solver/solver.h

**Language**: C | **Lines**: 365 | **Last modified**: 2026-06-26

## File-Level

_No discoveries yet._

## `class solver`

_No discoveries yet._

## `class model_converter`

_No discoveries yet._

## `class solver_factory`

### `solver_factory.operator`

_No discoveries yet._

### `solver_factory.translate`

_No discoveries yet._

## `mk_smt_strategic_solver_factory`

_No discoveries yet._

## `mk_smt2_solver`

_No discoveries yet._

## `class solver`

_No discoveries yet._

## `class scored_literal`

_No discoveries yet._

## `translate`

_No discoveries yet._

## `updt_params`

_No discoveries yet._

## `reset_params`

_No discoveries yet._

## `collect_param_descrs`

_No discoveries yet._

## `display_parameters`

_No discoveries yet._

## `push_params`

_No discoveries yet._

## `pop_params`

_No discoveries yet._

## `set_produce_models`

_No discoveries yet._

## `assert_expr`

_No discoveries yet._

## `assert_expr_core`

_No discoveries yet._

## `assert_expr`

_No discoveries yet._

## `set_phase`

_No discoveries yet._

## `move_to_front`

_No discoveries yet._

## `class phase`

_No discoveries yet._

## `get_phase`

_No discoveries yet._

## `set_phase`

_No discoveries yet._

## `assert_expr`

_No discoveries yet._

## `assert_expr`

_No discoveries yet._

## `assert_expr_core2`

_No discoveries yet._

## `push`

_No discoveries yet._

## `pop`

_No discoveries yet._

## `get_scope_level`

_No discoveries yet._

## `check_sat`

_No discoveries yet._

## `check_sat`

_No discoveries yet._

## `check_sat`

_No discoveries yet._

## `check_sat`

_No discoveries yet._

## `check_sat_cc`

_No discoveries yet._

## `set_progress_callback`

_No discoveries yet._

## `get_num_assertions`

_No discoveries yet._

## `get_assertion`

_No discoveries yet._

## `get_assertions`

_No discoveries yet._

## `get_assertions`

_No discoveries yet._

## `get_num_assumptions`

_No discoveries yet._

## `get_assumption`

_No discoveries yet._

## `get_consequences`

_No discoveries yet._

## `find_mutexes`

_No discoveries yet._

## `preferred_sat`

_No discoveries yet._

## `cube`

_No discoveries yet._

## `cube_vsids`

_No discoveries yet._

## `congruence_root`

_No discoveries yet._

## `congruence_next`

_No discoveries yet._

## `congruence_explain`

_No discoveries yet._

## `class solution`

_No discoveries yet._

## `solve_for`

_No discoveries yet._

## `display`

_No discoveries yet._

## `display_dimacs`

_No discoveries yet._

## `get_model_converter`

_No discoveries yet._

## `get_units`

_No discoveries yet._

## `get_units_core`

_No discoveries yet._

## `get_non_units`

_No discoveries yet._

## `get_trail`

_No discoveries yet._

## `get_assigned_literals`

_No discoveries yet._

## `get_assign_level`

_No discoveries yet._

## `is_relevant`

_No discoveries yet._

## `get_num_bool_vars`

_No discoveries yet._

## `get_bool_var`

_No discoveries yet._

## `bool_var2expr`

_No discoveries yet._

## `get_assignment`

_No discoveries yet._

## `get_activity`

_No discoveries yet._

## `was_eliminated`

_No discoveries yet._

## `pop_to_base_level`

_No discoveries yet._

## `setup_for_parallel`

_No discoveries yet._

## `set_preprocess`

_No discoveries yet._

## `set_max_conflicts`

_No discoveries yet._

## `get_max_conflicts`

_No discoveries yet._

## `get_levels`

_No discoveries yet._

## `get_backbone_candidates`

_No discoveries yet._

## `class scoped_push`

### `scoped_push.disable_pop`

_No discoveries yet._

## `check_sat_core`

_No discoveries yet._

## `get_consequences_core`

_No discoveries yet._

## `dump_state`

_No discoveries yet._

## `is_literal`

_No discoveries yet._


## `solver interface`

- solver exposes push/pop/get_scope_level as mandatory implementation hooks, while convenience check_sat overloads forward assumption vectors to the core pointer/count API.
  _(verified, source: exploration)_
  Dream report: `_dreams/20260730-212534Z-c8-t01-solver-header-scope-contract/`
## Cross-References

_No cross-cutting discoveries yet._
