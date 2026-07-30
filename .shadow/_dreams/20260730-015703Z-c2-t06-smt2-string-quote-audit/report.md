---
dream_id: "20260730-015703Z-c2-t06-smt2-string-quote-audit"
category: security audit
verdict: useful
base_commit: "b0ba1ac7096df44c2ef4b65c276066ea004f05c1"
branch: "dream/z3shadow/20260730-015703Z-c2-t06-smt2-string-quote-audit"
parent_branch: "master"
remote: "origin"
related_symbols:
  - "src/ast/ast_smt2_pp.cpp::smt2_pp_environment.pp_string_literal"
builds_on:
  []
---

# SMT2 string quote audit

## Motivation
ast_smt2_pp.cpp is an uncovered serialization path; SMT2 string output must not let embedded quotes terminate literals.

## Hypothesis
pp_string_literal should double embedded double quotes after zstring encoding instead of using raw quotes.

## Implementation
Added an adversarial static probe that extracts pp_string_literal and emulates the SMT-LIB quote-doubling loop.

## Commands Run
- `python dream_experiments/c2-t06-smt2-string-quote-audit.py` - exit code 0

## Evaluation
The probe verified output is wrapped in quotes and every encoded embedded quote is emitted as two quote characters.

Probe output:
```json
{"quote_doubling_verified": "\"a\"\"b\"\"\"", "uses_zstring_encode_first": true}
```

## Takeaways
pp_string_literal wraps zstring::encode() output in double quotes and doubles every embedded quote character, so SMT-LIB string delimiters are not emitted raw inside the literal body.

## Verdict Details
Useful: the branch contains a runnable adversarial probe and a verified shadow discovery tied to src/ast/ast_smt2_pp.cpp.
