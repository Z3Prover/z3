# Shadow: src/util/lbool.h

**Language**: C | **Lines**: 40 | **Last modified**: 2020-07-04

## File-Level

_No discoveries yet._

## `to_lbool`



- lbool negation and bool conversion are arithmetic over the enum ordinals -1/0/1; refactors that make lbool a scoped enum or reorder values must preserve those exact numeric assignments.
  _(verified, source: exploration, labels: [tech-debt])_
  Dream report: `_dreams/20260729-223918Z-t04-lbool-ordinal-contract/`
## Cross-References

_No cross-cutting discoveries yet._
