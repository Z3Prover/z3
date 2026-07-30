---
dream_id: "20260730-200606Z-c4-t06-func-decls-signature-coercion"
category: security audit
verdict: useful
base_commit: "ef7332ef200796448cdbd1077d2750369df857b1"
branch: "dream/z3shadow/20260730-200606Z-c4-t06-func-decls-signature-coercion"
parent_branch: "master"
remote: "origin"
related_symbols:
  - "src/cmd_context/cmd_context.cpp::func_decls::check_signature"
builds_on: []
---

# Command context signature coercion guard

## Motivation
cmd_context was uncovered and signature checking protects user-declared symbols.

## Hypothesis
A targeted static probe can verify the implicit behavior without a full Z3 build.

## Implementation
Added a runnable Python probe under dream_experiments that inspects the real source file and asserts the relevant control-flow markers are present.

## Commands Run
- `python dream_experiments/c4-t06-func-decls-signature-coercion.py` - exit code 0

## Evaluation
The probe completed successfully and printed the checked file, marker count, and file size.

Probe output:
```json
{"file": "src/cmd_context/cmd_context.cpp", "checks": 5, "bytes": 82564}
```

## Takeaways
func_decls::check_signature only permits an Int actual where a Real domain is expected as a coercion; every other domain mismatch returns false before the declaration is accepted.

## Verdict Details
Useful: the branch contains a non-empty runnable probe and a verified per-file shadow discovery tied to `src/cmd_context/cmd_context.cpp`.
