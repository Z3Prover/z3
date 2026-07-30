---
dream_id: "20260730-014854Z-c2-t02-nlsat-clause-hash-probe"
category: bug hunting
verdict: useful
base_commit: "b0ba1ac7096df44c2ef4b65c276066ea004f05c1"
branch: "dream/z3shadow/20260730-014854Z-c2-t02-nlsat-clause-hash-probe"
parent_branch: "master"
remote: "origin"
related_symbols:
  - "src/nlsat/nlsat_clause.cpp::clause.contains"
builds_on:
  []
---

# NLSAT clause hash probe

## Motivation
src/nlsat/nlsat_clause.cpp is uncovered error-prone SAT infrastructure; contains() correctness matters when clauses are learned and removed.

## Hypothesis
The m_var_hash field may be consulted by contains(), making stale hashes a correctness risk.

## Implementation
Added a probe that checks both contains overloads against clause.cpp and the m_var_hash accessors in clause.h.

## Commands Run
- `python dream_experiments/c2-t02-nlsat-clause-hash-probe.py` - exit code 0

## Evaluation
The probe found contains() linearly scans m_lits and ignores m_var_hash entirely, so stale hashes cannot change contains() answers inside clause.cpp.

Probe output:
```json
{"contains_overloads": 2, "contains_uses_var_hash": false}
```

## Takeaways
Both nlsat::clause::contains overloads linearly scan m_lits and never consult m_var_hash; var_hash is an external prefilter/metadata field, not part of contains() correctness.

## Verdict Details
Useful: the branch contains runnable code/probe changes and a verified shadow discovery tied to src/nlsat/nlsat_clause.cpp.
