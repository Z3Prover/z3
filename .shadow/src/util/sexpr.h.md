# Shadow: src/util/sexpr.h

**Language**: C | **Lines**: 82 | **Last modified**: 2020-09-13

## File-Level

_No discoveries yet._

## `class sexpr_manager`

_No discoveries yet._

## `class sexpr`

### `sexpr.display_atom`

_No discoveries yet._

### `sexpr.inc_ref`

_No discoveries yet._

### `sexpr.get_ref_count`

_No discoveries yet._

### `sexpr.get_line`

_No discoveries yet._

### `sexpr.get_pos`

_No discoveries yet._

### `sexpr.get_kind`

_No discoveries yet._

### `sexpr.is_composite`

_No discoveries yet._

### `sexpr.is_numeral`

_No discoveries yet._

### `sexpr.is_bv_numeral`

_No discoveries yet._

### `sexpr.is_string`

_No discoveries yet._

### `sexpr.is_keyword`

_No discoveries yet._

### `sexpr.is_symbol`

_No discoveries yet._

### `sexpr.get_bv_size`

_No discoveries yet._

### `sexpr.get_symbol`

_No discoveries yet._

### `sexpr.get_num_children`

_No discoveries yet._

### `sexpr.get_child`

_No discoveries yet._

### `sexpr.display`

_No discoveries yet._

## `class sexpr_manager`

### `sexpr_manager.del`

_No discoveries yet._

### `sexpr_manager.mk_composite`

_No discoveries yet._

### `sexpr_manager.mk_numeral`

_No discoveries yet._

### `sexpr_manager.mk_bv_numeral`

_No discoveries yet._

### `sexpr_manager.mk_string`

_No discoveries yet._

### `sexpr_manager.mk_string`

_No discoveries yet._

### `sexpr_manager.mk_keyword`

_No discoveries yet._

### `sexpr_manager.mk_symbol`

_No discoveries yet._

### `sexpr_manager.inc_ref`

_No discoveries yet._

### `sexpr_manager.dec_ref`

_No discoveries yet._


## `sexpr_manager`

- Every sexpr_manager mk_* factory defaults line and pos to UINT_MAX and sexpr only exposes raw get_line/get_pos accessors, so clients need to compare against UINT_MAX themselves to detect missing locations.
  _(verified, source: exploration, labels: [feature-gap])_
  Dream report: `_dreams/20260729-223759Z-t03-sexpr-location-sentinel/`

## `sexpr.has_location`

- A sexpr::has_location() helper can be implemented header-only by checking both m_line and m_pos against UINT_MAX, preserving the existing factory default sentinel contract.
  _(verified, source: exploration, labels: [feature-gap])_
  Dream report: `_dreams/20260730-015147Z-c2-t03-sexpr-has-location-helper/`
## Cross-References

_No cross-cutting discoveries yet._
