---
dream_id: "20260729-224200Z-t06-api-log-escaping-adversary"
category: security audit
verdict: useful
base_commit: "7c7ffbc9a48eb20c401357d320bcf27dd30b4819"
branch: "dream/z3shadow/20260729-224200Z-t06-api-log-escaping-adversary"
parent_branch: "master"
remote: "origin"
related_symbols:
  - "src/api/api_log.cpp::ll_escaped"
builds_on: []
---

# API log escaping adversary

## Motivation
src/api/api_log.cpp serializes user-visible API strings into replay logs, so adversarial quotes and newlines must not break record boundaries.

## Hypothesis
The log escaping operator should encode delimiters rather than pass quotes and control bytes through raw.

## Implementation
Added an adversarial escaping probe that mirrors the accepted-character set and checks quote/backslash/newline encoding.

## Commands Run
- `python dream_experiments/t06-api-log-escaping-adversary.py` - exit code 0

## Evaluation
The probe verified quotes, backslashes, and newlines are outside the raw allow-list and are emitted as three-digit escaped bytes.

Probe output:
```json
{"quote_backslash_newline_encoding": "a\\034\\092\\010 b", "space_allowed_raw": true}
```

## Takeaways
api_log ll_escaped leaves alphanumerics, spaces, and selected punctuation raw but encodes quotes, backslashes, and control bytes as backslash plus three decimal digits, preventing raw string-delimiter injection in log strings.

## Verdict Details
Useful: the branch contains a runnable probe and a verified shadow discovery tied to src/api/api_log.cpp.
