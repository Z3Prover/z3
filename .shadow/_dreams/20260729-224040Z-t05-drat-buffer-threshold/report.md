---
dream_id: "20260729-224040Z-t05-drat-buffer-threshold"
category: optimization
verdict: useful
base_commit: "7c7ffbc9a48eb20c401357d320bcf27dd30b4819"
branch: "dream/z3shadow/20260729-224040Z-t05-drat-buffer-threshold"
parent_branch: "master"
remote: "origin"
related_symbols:
  - "src/sat/sat_drat.cpp::drat.dump"
builds_on: []
---

# DRAT buffer threshold

## Motivation
src/sat/sat_drat.cpp writes proof traces on solver hot paths, so buffering policy affects proof-producing runs.

## Hypothesis
The text and binary DRAT dumpers use different flush thresholds that affect large-clause write granularity.

## Implementation
Added a static threshold probe for drat.dump and drat.bdump to extract buffer sizes and flush conditions.

## Commands Run
- `python dream_experiments/t05-drat-buffer-threshold.py` - exit code 0

## Evaluation
The probe established the text path reserves a 50-byte safety margin per next literal and the binary path fills all 10000 bytes.

Probe output:
```json
{"text_flush_when_len_exceeds": 9950, "binary_flush_when_full": 10000}
```

## Takeaways
Text DRAT dumping batches into a 10000-byte stack buffer and flushes before each next literal when len + 50 would exceed the buffer, while binary dumping waits for an exactly full buffer.

## Verdict Details
Useful: the branch contains a runnable probe and a verified shadow discovery tied to src/sat/sat_drat.cpp.
