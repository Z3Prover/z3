# Shadow: src/math/lp/nla_throttle.h

**Language**: C | **Lines**: 88 | **Last modified**: 2026-04-26

## File-Level

_No discoveries yet._

## `Nachmanson`

_No discoveries yet._

## `class nla_throttle`

_No discoveries yet._

## `class signature`

_No discoveries yet._

### `std.memcmp`

_No discoveries yet._

## `class signature_hash`

### `signature_hash.operator`

_No discoveries yet._

## `insert_new`

_No discoveries yet._

## `insert_new`

_No discoveries yet._

## `insert_new`

_No discoveries yet._

## `insert_new`

_No discoveries yet._

## `insert_new`

_No discoveries yet._

## `insert_new_impl`

_No discoveries yet._

## `pack_rational_sign`

_No discoveries yet._

## `normalize_sign`

_No discoveries yet._


## `nla_throttle.signature`

- nla_throttle signatures are fixed-width eight-slot records: construction zero-fills all slots, equality compares all eight slots, and hashing combines all eight slots, so every insert_new overload relies on unused slots remaining zero.
  _(verified, source: exploration)_
  Dream report: `_dreams/20260730-195156Z-c4-t01-nla-throttle-header-extension/`
## Cross-References

_No cross-cutting discoveries yet._
