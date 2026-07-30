# Shadow: src/model/model_evaluator.cpp

**Language**: C++ | **Lines**: 883 | **Last modified**: 2026-07-04

## File-Level

_No discoveries yet._

## `class evaluator_cfg`

### `evaluator_cfg.updt_params`

_No discoveries yet._

### `evaluator_cfg.p`

_No discoveries yet._

### `evaluator_cfg.evaluate`

_No discoveries yet._

### `evaluator_cfg.eval_fi`

_No discoveries yet._

### `evaluator_cfg.reduce_quantifier`

_No discoveries yet._

### `evaluator_cfg.th`

_No discoveries yet._

### `evaluator_cfg.reduce_app`

_No discoveries yet._

### `evaluator_cfg.contains_redex`

_No discoveries yet._

## `class has_redex`

_No discoveries yet._

## `class has_redex_finder`

### `has_redex_finder.operator`

_No discoveries yet._

### `has_redex_finder.operator`

_No discoveries yet._

### `has_redex_finder.operator`

_No discoveries yet._

### `has_redex_finder.has_redex`

_No discoveries yet._

### `has_redex_finder.has_redex`

_No discoveries yet._

### `has_redex_finder.has_redex`

_No discoveries yet._

## `ha`

_No discoveries yet._

## `reduce_app_core`

_No discoveries yet._

## `class pp`

_No discoveries yet._

## `_pp`

_No discoveries yet._

## `expand_as_array`

_No discoveries yet._

## `tmp`

_No discoveries yet._

## `ev`

_No discoveries yet._

## `expand_stores`

_No discoveries yet._

## `else_case`

_No discoveries yet._

## `args`

_No discoveries yet._

## `reduce_macro`

_No discoveries yet._

## `get_macro`

_No discoveries yet._

## `subst`

_No discoveries yet._

## `util`

_No discoveries yet._

## `evaluate_partial_theory_func`

_No discoveries yet._

## `f_ui`

_No discoveries yet._

## `vs`

_No discoveries yet._

## `vs`

_No discoveries yet._

## `max_steps_exceeded`

_No discoveries yet._

## `rewriter_exception`

_No discoveries yet._

## `mk_array_eq`

_No discoveries yet._

## `else1`

_No discoveries yet._

## `conj`

_No discoveries yet._

## `mk_array_eq_core`

_No discoveries yet._

## `s1`

_No discoveries yet._

## `s2`

_No discoveries yet._

## `class args_eq`

### `args_eq.operator`

_No discoveries yet._

## `class args_hash`

### `args_hash.operator`

_No discoveries yet._

### `args_hash.get_composite_hash`

_No discoveries yet._

### `args_hash.operator`

_No discoveries yet._

## `mk_array_eq_core`

_No discoveries yet._

## `ah`

_No discoveries yet._

## `ae`

_No discoveries yet._

## `table1`

_No discoveries yet._

## `table2`

_No discoveries yet._

## `compare`

_No discoveries yet._

## `args_are_values`

_No discoveries yet._

## `extract_array_func_interp`

_No discoveries yet._

## `store`

_No discoveries yet._

## `store`

_No discoveries yet._

## `class model_evaluator`

### `model_evaluator.expand_stores`

_No discoveries yet._

### `model_evaluator.reset`

_No discoveries yet._

### `model_evaluator.m`

_No discoveries yet._

### `model_evaluator.updt_params`

_No discoveries yet._

### `model_evaluator.get_param_descrs`

_No discoveries yet._

### `model_evaluator.set_model_completion`

_No discoveries yet._

### `model_evaluator.get_model_completion`

_No discoveries yet._

### `model_evaluator.set_expand_array_equalities`

_No discoveries yet._

### `model_evaluator.get_num_steps`

_No discoveries yet._

### `model_evaluator.cleanup`

_No discoveries yet._

### `model_evaluator.reset`

_No discoveries yet._

### `model_evaluator.reset`

_No discoveries yet._

### `model_evaluator.operator`

_No discoveries yet._

### `model_evaluator.operator`

_No discoveries yet._

## `result`

_No discoveries yet._

### `model_evaluator.operator`

_No discoveries yet._

## `rs`

_No discoveries yet._

### `model_evaluator.is_true`

_No discoveries yet._

## `tmp`

_No discoveries yet._

## `eval`

_No discoveries yet._

### `model_evaluator.is_false`

_No discoveries yet._

## `tmp`

_No discoveries yet._

## `eval`

_No discoveries yet._

### `model_evaluator.is_true`

_No discoveries yet._

### `model_evaluator.are_equal`

_No discoveries yet._

## `t1`

_No discoveries yet._

## `m`

_No discoveries yet._

### `model_evaluator.eval`

_No discoveries yet._

### `model_evaluator.eval`

_No discoveries yet._

## `tmp`

_No discoveries yet._

## `eval`

_No discoveries yet._


## `evaluator_cfg.expand_as_array`

- model_evaluator caches expanded as-array definitions in m_def_cache only within one evaluator reset cycle; imp::reset clears the cache, so repeated top-level eval calls recompute those expansions.
  _(verified, source: exploration, labels: [performance])_
  Dream report: `_dreams/20260730-015431Z-c2-t05-model-evaluator-cache-scope/`
## Cross-References

_No cross-cutting discoveries yet._
