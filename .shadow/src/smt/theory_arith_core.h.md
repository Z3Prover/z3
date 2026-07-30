# Shadow: src/smt/theory_arith_core.h

**Language**: C | **Lines**: 3576 | **Last modified**: 2026-07-29

## File-Level

_No discoveries yet._

## `val`

_No discoveries yet._

## `val`

_No discoveries yet._

## `default_exception`

_No discoveries yet._

## `_sc`

_No discoveries yet._

## `_sc`

_No discoveries yet._

## `internalize_term_core`

_No discoveries yet._

## `val`

_No discoveries yet._

## `internalize_numeral`

_No discoveries yet._

## `_sc`

_No discoveries yet._

## `internalize_mul_core`

_No discoveries yet._

## `expr2var`

_No discoveries yet._

## `mk_var`

_No discoveries yet._

## `r`

_No discoveries yet._

## `r`

_No discoveries yet._

## `r`

_No discoveries yet._

## `s_ante`

_No discoveries yet._

## `p_ante`

_No discoveries yet._

## `body`

_No discoveries yet._

## `div`

_No discoveries yet._

## `div`

_No discoveries yet._

## `eqz`

_No discoveries yet._

## `eq`

_No discoveries yet._

## `div_ge`

_No discoveries yet._

## `j`

_No discoveries yet._

## `mod_j`

_No discoveries yet._

## `lit`

_No discoveries yet._

## `dltz`

_No discoveries yet._

## `to_r`

_No discoveries yet._

## `diff`

_No discoveries yet._

## `lo`

_No discoveries yet._

## `hi`

_No discoveries yet._

## `expr2var`

_No discoveries yet._

## `expr2var`

_No discoveries yet._

## `expr2var`

_No discoveries yet._

## `_sc`

_No discoveries yet._

## `val`

_No discoveries yet._

## `internalize_numeral`

_No discoveries yet._

## `mk_var`

_No discoveries yet._

## `ival`

_No discoveries yet._

## `class theory_arith`

_No discoveries yet._

## `internalize_add`

_No discoveries yet._

## `internalize_mul`

_No discoveries yet._

## `internalize_div`

_No discoveries yet._

## `internalize_idiv`

_No discoveries yet._

## `internalize_mod`

_No discoveries yet._

## `internalize_rem`

_No discoveries yet._

## `internalize_to_real`

_No discoveries yet._

## `internalize_to_int`

_No discoveries yet._

## `internalize_numeral`

_No discoveries yet._

## `internalize_sub`

_No discoveries yet._

## `mk_binary_op`

_No discoveries yet._

## `mk_var`

_No discoveries yet._

## `expr2var`

_No discoveries yet._

## `mk_var`

_No discoveries yet._

## `mk_var`

_No discoveries yet._

## `l1`

_No discoveries yet._

## `l2`

_No discoveries yet._

## `default_exception`

_No discoveries yet._

## `k`

_No discoveries yet._

## `val`

_No discoveries yet._

## `process_atoms`

_No discoveries yet._

## `alloc`

_No discoveries yet._

## `get_value`

_No discoveries yet._

## `get_value`

_No discoveries yet._

## `select_blands_pivot_core`

_No discoveries yet._

## `select_smallest_var`

_No discoveries yet._

## `select_greatest_error_var`

_No discoveries yet._

## `select_least_error_var`

_No discoveries yet._

## `select_smallest_var`

_No discoveries yet._

## `ante`

_No discoveries yet._

## `ante`

_No discoveries yet._

## `inv_coeff`

_No discoveries yet._

## `l`

_No discoveries yet._

## `ante`

_No discoveries yet._

## `two`

_No discoveries yet._

## `alloc`

_No discoveries yet._


## `theory_arith::internalize_atom`

- theory_arith_core maps division, integer division, and remainder by zero into dedicated underspecified div0/idiv0/rem0 terms instead of rejecting the expression during internalization.
  _(verified, source: exploration, labels: [feature-gap])_
  Dream report: `_dreams/20260730-213540Z-c8-t05-arith-core-underspecified-zero-ops/`
## Cross-References

_No cross-cutting discoveries yet._
