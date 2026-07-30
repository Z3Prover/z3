---
dream_id: "20260730-201835Z-c5-t01-polynomial-cache-api-surface"
category: investigation
verdict: useful
base_commit: "73d582a5cd469c7669e283532c5efd6066dcd559"
branch: "dream/z3shadow/20260730-201835Z-c5-t01-polynomial-cache-api-surface"
parent_branch: "dream/z3shadow/20260730-195514Z-c4-t02-polynomial-cache-factor"
remote: "origin"
related_symbols:
  - "src/math/polynomial/polynomial_cache.h::polynomial::cache"
builds_on:   - "20260730-195514Z-c4-t02-polynomial-cache-factor"
---

# Polynomial cache API surface follow-up

## Motivation
Compounds cycle-4 polynomial cache factor replay by checking which cache operations are visible in the public header.

## Compounding Delta
Built on `dream/z3shadow/20260730-195514Z-c4-t02-polynomial-cache-factor` (base commit `73d582a5cd469c7669e283532c5efd6066dcd559`), extended the parent probe when present, and added this follow-up check for `src/math/polynomial/polynomial_cache.h`.

## Hypothesis
A targeted static probe can verify the implicit behavior without a full Z3 build.

## Implementation
Added a runnable Python probe under dream_experiments that inspects the real source file and asserts the relevant control-flow markers are present.

## Commands Run
- `python dream_experiments/c5-t01-polynomial-cache-api-surface.py` - exit code 0

## Evaluation
The probe completed successfully and printed the checked file, marker count, and file size.

Probe output:
```json
{"file": "src/math/polynomial/polynomial_cache.h", "checks": 5, "bytes": 966}
```

## Takeaways
polynomial::cache exposes cache hits for psc_chain via contains_chain but not for factorization; callers can probe chain cache membership but factor cache reuse is only observable by calling factor().

## Verdict Details
Useful: the branch contains a non-empty runnable probe and a verified per-file shadow discovery tied to `src/math/polynomial/polynomial_cache.h`.
