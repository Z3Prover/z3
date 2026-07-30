# Shadow: src/ast/rewriter/rewriter.cpp

**Language**: C++ | **Lines**: 424 | **Last modified**: 2026-07-14

## File-Level

_No discoveries yet._

### `rewriter_core.init_cache_stack`

_No discoveries yet._

### `rewriter_core.del_cache_stack`

_No discoveries yet._

### `rewriter_core.rewrites_from`

_No discoveries yet._

### `rewriter_core.rewrites_to`

_No discoveries yet._

### `rewriter_core.cache_shifted_result`

_No discoveries yet._

### `rewriter_core.cache_result`

_No discoveries yet._

### `rewriter_core.get_cache_size`

_No discoveries yet._

### `rewriter_core.reset_cache`

_No discoveries yet._

### `rewriter_core.free_memory`

_No discoveries yet._

### `rewriter_core.begin_scope`



- rewriter_core caches are indexed by scope depth: begin_scope reuses or allocates one cache per level, end_scope resets the current level and restores the previous cache, and reset_cache only resets the base cache.
  _(verified, source: exploration, labels: [tech-debt])_
  Dream report: `_dreams/20260730-043224Z-c3-t04-rewriter-cache-scope-stack/`
### `rewriter_core.end_scope`

_No discoveries yet._

### `rewriter_core.is_child_of_top_frame`

_No discoveries yet._

### `rewriter_core.elim_reflex_prs`

_No discoveries yet._

### `rewriter_core.reset`

_No discoveries yet._

### `rewriter_core.cleanup`

_No discoveries yet._

### `rewriter_core.display_stack`

_No discoveries yet._

### `var_shifter_core.visit`

_No discoveries yet._

### `var_shifter_core.process_app`

_No discoveries yet._

### `var_shifter_core.process_quantifier`

_No discoveries yet._

### `var_shifter_core.main_loop`

_No discoveries yet._

### `var_shifter.operator`

_No discoveries yet._

### `var_shifter.process_var`

_No discoveries yet._

### `inv_var_shifter.operator`

_No discoveries yet._

### `inv_var_shifter.process_var`

_No discoveries yet._

## Cross-References

_No cross-cutting discoveries yet._
