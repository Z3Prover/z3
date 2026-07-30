---
dream_id: "20260730-205111Z-c6-t05-upolynomial-prime-conversion-guards"
category: optimization
verdict: useful
base_commit: "fd5ae54bdd512d5ca83fbdb683a8f61823bc6f2e"
branch: "dream/z3shadow/20260730-205111Z-c6-t05-upolynomial-prime-conversion-guards"
parent_branch: "master"
remote: "origin"
related_symbols:
  - "src/math/polynomial/upolynomial_factorization.cpp::get_prime_as_uint"
builds_on: []
---

# Univariate factorization prime guards

## Motivation
polynomial factorization was uncovered and prime conversion protects modular algorithms.

## Hypothesis
A targeted static probe can verify the implicit behavior without a full Z3 build.

## Implementation
Added a runnable Python probe under dream_experiments that inspects the real source file and asserts the relevant control-flow markers are present.

## Commands Run
- `python dream_experiments/c6-t05-upolynomial-prime-conversion-guards.py` - exit code 0

## Evaluation
The probe completed successfully and printed the checked file, marker count, and file size.

Probe output:
```json
{"file": "src/math/polynomial/upolynomial_factorization.cpp", "checks": 4, "bytes": 51664}
```

## Takeaways
upolynomial factorization rejects primes that cannot round-trip from the numeral manager to uint64_t and then to unsigned, throwing before modular factorization uses a truncated prime.

## Verdict Details
Useful: the branch contains a non-empty runnable probe and a verified per-file shadow discovery tied to `src/math/polynomial/upolynomial_factorization.cpp`.
