# Shadow: src/parsers/smt2/smt2scanner.cpp

**Language**: C++ | **Lines**: 407 | **Last modified**: 2026-07-02

## File-Level

_No discoveries yet._

### `scanner.next`

_No discoveries yet._

## `scanner_exception`

_No discoveries yet._

### `scanner.read_comment`

_No discoveries yet._

### `scanner.read_multiline_comment`



- read_multiline_comment treats the first |# as the terminator and keeps no nesting depth, while still calling new_line() for embedded newlines; malformed nested-looking comments resume scanning after the inner close.
  _(verified, source: exploration)_
  Dream report: `_dreams/20260729-223630Z-t02-smt2-comment-boundary/`
### `scanner.read_quoted_symbol`

_No discoveries yet._

## `scanner_exception`

_No discoveries yet._

### `scanner.read_symbol_core`

_No discoveries yet._

### `scanner.read_symbol`

_No discoveries yet._

## `read_symbol_core`

_No discoveries yet._

### `scanner.read_number`

_No discoveries yet._

## `q`

_No discoveries yet._

### `scanner.read_signed_number`

_No discoveries yet._

## `read_symbol_core`

_No discoveries yet._

### `scanner.read_string`

_No discoveries yet._

## `scanner_exception`

_No discoveries yet._

### `scanner.read_bv_literal`

_No discoveries yet._

## `scanner_exception`

_No discoveries yet._

## `scanner_exception`

_No discoveries yet._

## `scanner_exception`

_No discoveries yet._

### `scanner.scan`

_No discoveries yet._

## `read_quoted_symbol`

_No discoveries yet._

## `read_symbol`

_No discoveries yet._

## `read_string`

_No discoveries yet._

## `read_number`

_No discoveries yet._

## `read_symbol`

_No discoveries yet._

## `read_signed_number`

_No discoveries yet._

## `ex`

_No discoveries yet._

### `scanner.reset_input`

_No discoveries yet._

## Cross-References

_No cross-cutting discoveries yet._
