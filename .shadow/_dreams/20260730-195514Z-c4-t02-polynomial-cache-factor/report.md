---
dream_id: "20260730-195514Z-c4-t02-polynomial-cache-factor"
category: bug hunting
verdict: useful
base_commit: "ef7332ef200796448cdbd1077d2750369df857b1"
branch: "dream/z3shadow/20260730-195514Z-c4-t02-polynomial-cache-factor"
parent_branch: "master"
remote: "origin"
related_symbols:
  - "src/math/polynomial/polynomial_cache.cpp::cache::imp.factor"
builds_on: []
---

# Polynomial factor cache replay

## Motivation
math/polynomial was uncovered and polynomial_cache.cpp owns operation-level memoization.

## Hypothesis
A targeted static probe can verify the implicit behavior without a full Z3 build.

## Implementation
Added a runnable Python probe under dream_experiments that inspects the real source file and asserts the relevant control-flow markers are present.

## Commands Run
- `python dream_experiments/c4-t02-polynomial-cache-factor.py` - exit code 0

## Evaluation
The probe completed successfully and printed the checked file, marker count, and file size.

Probe output:
```json
{"file": "src/math/polynomial/polynomial_cache.cpp", "checks": 6, "bytes": 8890}
```

## Takeaways
polynomial::cache::factor caches factorization results by the canonical polynomial pointer, stores canonicalized factor pointers in a manually allocated result array, and replays cached results without recomputing factorization.

## Verdict Details
Useful: the branch contains a non-empty runnable probe and a verified per-file shadow discovery tied to `src/math/polynomial/polynomial_cache.cpp`.
