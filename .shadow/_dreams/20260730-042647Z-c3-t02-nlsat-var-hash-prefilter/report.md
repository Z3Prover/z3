---
dream_id: "20260730-042647Z-c3-t02-nlsat-var-hash-prefilter"
category: bug hunting
verdict: useful
base_commit: "3cdd90a320308c6d1a1ef6ce62d4ed527ca4d070"
branch: "dream/z3shadow/20260730-042647Z-c3-t02-nlsat-var-hash-prefilter"
parent_branch: "dream/z3shadow/20260730-014854Z-c2-t02-nlsat-clause-hash-probe"
remote: "origin"
related_symbols:
  - "src/nlsat/nlsat_simplify.cpp::simplifier.subsumes"
builds_on:   - "20260730-014854Z-c2-t02-nlsat-clause-hash-probe"
---

# NLSAT var-hash prefilter follow-up

## Motivation
Cycle 2 showed clause::contains ignores m_var_hash; this follow-up compounds by tracing where that hash is actually consumed in nlsat_simplify.cpp.

## Compounding Delta
Built on `dream/z3shadow/20260730-014854Z-c2-t02-nlsat-clause-hash-probe` and extended the parent probe/code path: Extended the cycle-2 nlsat probe and added a new probe that checks compute_occurs hash construction and the subsumes hash subset test.

## Hypothesis
The variable hash is a lossy prefilter for subsumption, so hash collisions should cost extra scans but not change contains() correctness.

## Implementation
Extended the cycle-2 nlsat probe and added a new probe that checks compute_occurs hash construction and the subsumes hash subset test.

## Commands Run
- `python dream_experiments/c3-t02-nlsat-var-hash-prefilter.py` - exit code 0

## Evaluation
The probe verified compute_occurs ORs variables modulo 32 into m_var_hash, and subsumes checks hash subset before scanning literals.

Probe output:
```json
{"hash_bits_modulo": 32, "subsumption_uses_subset_prefilter": true, "contains_still_hash_independent": true}
```

## Takeaways
nlsat_simplify uses clause::var_hash as a 32-bit modulo prefilter for subsumption before literal scans; collisions can cause extra subsumption work but cannot make clause::contains depend on the hash.

## Verdict Details
Useful: the branch contains runnable probe/code changes and a verified shadow discovery tied to src/nlsat/nlsat_simplify.cpp.
