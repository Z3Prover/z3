# Shadow: src/nlsat/nlsat_clause.cpp

**Language**: C++ | **Lines**: 52 | **Last modified**: 2026-07-02

## File-Level

_No discoveries yet._

### `clause.contains`



- Both nlsat::clause::contains overloads linearly scan m_lits and never consult m_var_hash; var_hash is an external prefilter/metadata field, not part of contains() correctness.
  _(verified, source: exploration)_
  Dream report: `_dreams/20260730-014854Z-c2-t02-nlsat-clause-hash-probe/`
### `clause.contains`

_No discoveries yet._

## Cross-References

_No cross-cutting discoveries yet._
