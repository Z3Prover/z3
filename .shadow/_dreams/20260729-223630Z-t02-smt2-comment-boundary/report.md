---
dream_id: "20260729-223630Z-t02-smt2-comment-boundary"
category: bug hunting
verdict: useful
base_commit: "7c7ffbc9a48eb20c401357d320bcf27dd30b4819"
branch: "dream/z3shadow/20260729-223630Z-t02-smt2-comment-boundary"
parent_branch: "master"
remote: "origin"
related_symbols:
  - "src/parsers/smt2/smt2scanner.cpp::scanner.read_multiline_comment"
builds_on: []
---

# SMT2 multiline comment boundary

## Motivation
smt2scanner.cpp owns SMT-LIB token boundaries; comment recovery affects every parser error that follows a malformed block comment.

## Hypothesis
The scanner may support nested #| |# comments or may stop at the first closing delimiter.

## Implementation
Added an assertion probe that extracts read_multiline_comment and checks for the close-delimiter condition and absence of nesting state.

## Commands Run
- `python dream_experiments/t02-smt2-comment-boundary.py` - exit code 0

## Evaluation
The probe verified the scanner is first-close only, so error positions after nested-looking comments should be interpreted with that contract.

Probe output:
```json
{"first_close_index": 18, "tracks_nesting": false, "updates_newlines": true}
```

## Takeaways
read_multiline_comment treats the first |# as the terminator and keeps no nesting depth, while still calling new_line() for embedded newlines; malformed nested-looking comments resume scanning after the inner close.

## Verdict Details
Useful: the branch contains a runnable probe and a verified shadow discovery tied to src/parsers/smt2/smt2scanner.cpp.
