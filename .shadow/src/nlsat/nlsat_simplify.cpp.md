# Shadow: src/nlsat/nlsat_simplify.cpp

**Language**: C++ | **Lines**: 829 | **Last modified**: 2026-07-02

## File-Level

_No discoveries yet._

## `class simplify`

### `simplify.operator`

_No discoveries yet._

### `simplify.simplify_literals`

_No discoveries yet._

### `simplify.lits`

_No discoveries yet._

### `simplify.p`

_No discoveries yet._

### `simplify.update_clauses`

_No discoveries yet._

### `simplify.split_factors`

_No discoveries yet._

### `simplify.elim_uncnstr`

_No discoveries yet._

### `simplify.is_unconstrained`

_No discoveries yet._

### `simplify.A`

_No discoveries yet._

### `simplify.compute_occurs`

_No discoveries yet._

### `simplify.compute_occurs`

_No discoveries yet._

### `simplify.cleanup_removed`

_No discoveries yet._

### `simplify.unit_subsumption_simplify`

_No discoveries yet._

### `simplify.subsumption_simplify`

_No discoveries yet._

### `simplify.subsumes`

_No discoveries yet._

### `simplify.subsumes`

_No discoveries yet._

### `simplify.fm`

_No discoveries yet._

### `simplify.cleanup_removed`

_No discoveries yet._

### `simplify.is_invertible`

_No discoveries yet._

### `simplify.apply_fm`

_No discoveries yet._

### `simplify.A`

_No discoveries yet._

### `simplify.l`

_No discoveries yet._

### `simplify.h`

_No discoveries yet._

### `simplify.apply_fm_inequality`

_No discoveries yet._

### `simplify.C`

_No discoveries yet._

### `simplify.substitute_var`

_No discoveries yet._

### `simplify.substitute_var`

_No discoveries yet._

### `simplify.pr`

_No discoveries yet._

### `simplify.ps`

_No discoveries yet._

### `simplify.apply_fm_equality`

_No discoveries yet._

### `simplify.apply_fm_equality`

_No discoveries yet._

### `simplify.A`

_No discoveries yet._

### `simplify.is_single_poly`

_No discoveries yet._

### `simplify.is_unit`

_No discoveries yet._

### `simplify.operator`

_No discoveries yet._


## `simplifier.subsumes`

- nlsat_simplify uses clause::var_hash as a 32-bit modulo prefilter for subsumption before literal scans; collisions can cause extra subsumption work but cannot make clause::contains depend on the hash.
  _(verified, source: exploration, labels: [performance])_
  Dream report: `_dreams/20260730-042647Z-c3-t02-nlsat-var-hash-prefilter/`
## Cross-References

_No cross-cutting discoveries yet._
