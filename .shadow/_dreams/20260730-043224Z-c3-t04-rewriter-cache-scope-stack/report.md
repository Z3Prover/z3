---
dream_id: "20260730-043224Z-c3-t04-rewriter-cache-scope-stack"
category: refactoring
verdict: useful
base_commit: "3c0773d811ba972a15f614d9e8dfb46eee1286b4"
branch: "dream/z3shadow/20260730-043224Z-c3-t04-rewriter-cache-scope-stack"
parent_branch: "master"
remote: "origin"
related_symbols:
  - "src/ast/rewriter/rewriter.cpp::rewriter_core.begin_scope"
builds_on: []
---

# Rewriter cache scope stack

## Motivation
src/ast/rewriter was untouched and rewriter.cpp has manual cache-stack lifetime management that is easy to disturb during refactors.

## Hypothesis
Cache objects are reused by scope depth and require balanced begin/end discipline rather than per-scope allocation every time.

## Implementation
Added a static probe over rewriter_core cache-stack methods to verify allocation, reset, restore, and cleanup contracts.

## Commands Run
- `python dream_experiments/c3-t04-rewriter-cache-scope-stack.py` - exit code 0

## Evaluation
The probe confirmed begin_scope reuses/allocates caches by level, end_scope resets the current cache and restores the previous level, and reset_cache only resets level 0.

Probe output:
```json
{"cache_reused_by_scope_depth": true, "end_scope_restores_previous_level": true}
```

## Takeaways
rewriter_core caches are indexed by scope depth: begin_scope reuses or allocates one cache per level, end_scope resets the current level and restores the previous cache, and reset_cache only resets the base cache.

## Verdict Details
Useful: the branch contains runnable probe/code changes and a verified shadow discovery tied to src/ast/rewriter/rewriter.cpp.
