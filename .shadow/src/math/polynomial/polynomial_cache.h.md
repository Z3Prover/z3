# Shadow: src/math/polynomial/polynomial_cache.h

**Language**: C | **Lines**: 43 | **Last modified**: 2026-07-02

## File-Level

_No discoveries yet._

## `class cache`

_No discoveries yet._

## `class imp`

_No discoveries yet._

## `m`

_No discoveries yet._

## `pm`

_No discoveries yet._

## `mk_unique`

_No discoveries yet._

## `contains`

_No discoveries yet._

## `contains_chain`

_No discoveries yet._

## `psc_chain`

_No discoveries yet._

## `factor`

_No discoveries yet._

## `reset`

_No discoveries yet._


## `polynomial::cache`

- polynomial::cache exposes cache hits for psc_chain via contains_chain but not for factorization; callers can probe chain cache membership but factor cache reuse is only observable by calling factor().
  _(verified, source: exploration, labels: [feature-gap])_
  Dream report: `_dreams/20260730-201835Z-c5-t01-polynomial-cache-api-surface/`
## Cross-References

_No cross-cutting discoveries yet._
