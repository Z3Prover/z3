---
dream_id: "20260730-210621Z-c7-t02-dd-fdd-unexpected-variable-assert"
category: bug hunting
verdict: useful
base_commit: "4d646fd910422ce0d78c3b0e3b8edcdfed3fb950"
branch: "dream/z3shadow/20260730-210621Z-c7-t02-dd-fdd-unexpected-variable-assert"
parent_branch: "master"
remote: "origin"
related_symbols:
  - "src/math/dd/dd_fdd.cpp::fdd::contains"
builds_on: []
---

# FDD unexpected variable assertion

## Motivation
math/dd fdd code was uncovered and contains() is a validation path.

## Hypothesis
A targeted static probe can verify the implicit behavior without a full Z3 build.

## Implementation
Added a runnable Python probe under dream_experiments that inspects the real source file and asserts the relevant control-flow markers are present.

## Commands Run
- `python dream_experiments/c7-t02-dd-fdd-unexpected-variable-assert.py` - exit code 0

## Evaluation
The probe completed successfully and printed the checked file, marker count, and file size.

Probe output:
```json
{"file": "src/math/dd/dd_fdd.cpp", "checks": 5, "bytes": 10323}
```

## Takeaways
dd::fdd::contains asserts that every traversed BDD variable maps back to an FDD position; an unexpected BDD variable is a debug-only contract violation rather than a recoverable false result.

## Verdict Details
Useful: the branch contains a non-empty runnable probe and a verified per-file shadow discovery tied to `src/math/dd/dd_fdd.cpp`.
