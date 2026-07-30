# Shadow: src/sat/sat_clause.cpp

**Language**: C++ | **Lines**: 252 | **Last modified**: 2026-07-02

## File-Level

_No discoveries yet._

### `clause.approx`

_No discoveries yet._

### `clause.update_approx`

_No discoveries yet._

### `clause.check_approx`

_No discoveries yet._

### `clause.contains`

_No discoveries yet._

### `clause.contains`

_No discoveries yet._

### `clause.elim`

_No discoveries yet._

### `clause.shrink`

_No discoveries yet._

### `clause.restore`

_No discoveries yet._

### `clause.satisfied_by`

_No discoveries yet._

### `clause.get_new_offset`

_No discoveries yet._

### `clause.set_new_offset`

_No discoveries yet._

### `tmp_clause.set`

_No discoveries yet._

### `clause_allocator.finalize`

_No discoveries yet._

### `clause_allocator.get_clause`

_No discoveries yet._

### `clause_allocator.get_offset`

_No discoveries yet._

### `clause_allocator.mk_clause`

_No discoveries yet._

### `clause_allocator.copy_clause`

_No discoveries yet._

### `clause_allocator.del_clause`

_No discoveries yet._

### `clause_wrapper.contains`

_No discoveries yet._

### `clause_wrapper.contains`

_No discoveries yet._


## `clause::get_new_offset`

- sat::clause relocation on 64-bit stores a synthetic offset in the first two literal slots, so callers must only use get_new_offset/set_new_offset on clauses whose storage has at least two literal slots available.
  _(verified, source: exploration, labels: [tech-debt])_
  Dream report: `_dreams/20260730-202106Z-c5-t02-sat-clause-offset-packing/`
## Cross-References

_No cross-cutting discoveries yet._
