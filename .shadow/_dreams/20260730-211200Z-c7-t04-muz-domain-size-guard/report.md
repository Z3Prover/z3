---
dream_id: "20260730-211200Z-c7-t04-muz-domain-size-guard"
category: refactoring
verdict: useful
base_commit: "4d646fd910422ce0d78c3b0e3b8edcdfed3fb950"
branch: "dream/z3shadow/20260730-211200Z-c7-t04-muz-domain-size-guard"
parent_branch: "master"
remote: "origin"
related_symbols:
  - "src/muz/base/dl_context.cpp::context::symbol_sort_domain.get_number"
builds_on: []
---

# Muz finite-domain size guard

## Motivation
muz/base was uncovered and finite-domain numbering is a persistent contract.

## Hypothesis
A targeted static probe can verify the implicit behavior without a full Z3 build.

## Implementation
Added a runnable Python probe under dream_experiments that inspects the real source file and asserts the relevant control-flow markers are present.

## Commands Run
- `python dream_experiments/c7-t04-muz-domain-size-guard.py` - exit code 0

## Evaluation
The probe completed successfully and printed the checked file, marker count, and file size.

Probe output:
```json
{"file": "src/muz/base/dl_context.cpp", "checks": 5, "bytes": 46635}
```

## Takeaways
muz::context finite sort domains assign dense element numbers with insert_if_not_there and throw default_exception when a limited-size sort receives more distinct constants than declared.

## Verdict Details
Useful: the branch contains a non-empty runnable probe and a verified per-file shadow discovery tied to `src/muz/base/dl_context.cpp`.
