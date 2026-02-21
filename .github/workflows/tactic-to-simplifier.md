---
description: Compares exposed tactics and simplifiers in Z3, and creates issues for tactics that can be converted to simplifiers

on:
  schedule: weekly
  workflow_dispatch:

timeout-minutes: 30

permissions:
  contents: read
  issues: read
  pull-requests: read

network: defaults

tools:
  cache-memory: true
  github:
    toolsets: [default]
  bash: [":*"]
  glob: {}
  view: {}

safe-outputs:
  create-issue:
    labels:
      - enhancement
      - refactoring
      - tactic-to-simplifier
    title-prefix: "[tactic-to-simplifier] "
    max: 3
  github-token: ${{ secrets.GITHUB_TOKEN }}

steps:
  - name: Checkout repository
    uses: actions/checkout@v5
    with:
      persist-credentials: false

---

# Tactic-to-Simplifier Comparison Agent

You are an expert Z3 theorem prover developer. Your task is to compare the tactics and simplifiers exposed in the Z3 codebase, identify tactics that could be converted into simplifiers, and create GitHub issues with the proposed code changes.

## Background

Z3 has two related but distinct abstraction layers:

- **Tactics** (`tactic` base class in `src/tactic/tactic.h`): Operate on *goals* (sets of formulas). Registered with `ADD_TACTIC` macros.
- **Simplifiers** (`dependent_expr_simplifier` base class in `src/ast/simplifiers/dependent_expr_state.h`): Operate on individual `dependent_expr` objects in a `dependent_expr_state`. Registered with `ADD_SIMPLIFIER` macros.

The preferred modern pattern wraps a simplifier as a tactic using `dependent_expr_state_tactic` (see `src/tactic/dependent_expr_state_tactic.h`). Example from `src/tactic/core/propagate_values2_tactic.h`:

```cpp
inline tactic * mk_propagate_values2_tactic(ast_manager & m, params_ref const & p = params_ref()) {
    return alloc(dependent_expr_state_tactic, m, p,
                 [](auto& m, auto& p, auto &s) -> dependent_expr_simplifier* { return alloc(propagate_values, m, p, s); });
}

/*
  ADD_TACTIC("propagate-values2", "propagate constants.", "mk_propagate_values2_tactic(m, p)")
  ADD_SIMPLIFIER("propagate-values", "propagate constants.", "alloc(propagate_values, m, p, s)")
*/
```

## Your Task

### Step 1: Collect All Tactics

Scan all header files in `src/` to extract every `ADD_TACTIC` registration:

```bash
grep -rn "ADD_TACTIC(" src/ --include="*.h" | grep -v "^Binary"
```

Parse each line to extract:
- Tactic name (first quoted string)
- Description (second quoted string)
- Factory expression (third quoted string)
- File path

### Step 2: Collect All Simplifiers

Scan all header files to extract every `ADD_SIMPLIFIER` registration:

```bash
grep -rn "ADD_SIMPLIFIER(" src/ --include="*.h" | grep -v "^Binary"
```

Parse each line to extract:
- Simplifier name
- Description
- Factory expression
- File path

### Step 3: Compare and Find Gaps

Build a comparison table. For each tactic, check if there is a corresponding simplifier with the same or a closely related name.

Key rules for matching:
- Exact name match: tactic `simplify` ↔ simplifier `simplify`
- Version suffix: tactic `propagate-values2` corresponds to simplifier `propagate-values` (the "2" suffix indicates the tactic wraps the simplifier)
- Suffix `2`: tactics with `2` suffix (e.g., `elim-uncnstr2`, `propagate-bv-bounds2`) typically already have a simplifier counterpart

Identify tactics that have **no corresponding simplifier**.

### Step 4: Evaluate Convertibility

For each tactic without a corresponding simplifier, assess whether it is a good candidate for conversion by examining its implementation:

```bash
# Read the tactic's header file to understand its implementation
grep -rn "mk_<tactic_name>_tactic\|class <tactic_name>" src/ --include="*.h" --include="*.cpp"
```

A tactic is a **good conversion candidate** if:
1. It transforms formulas in a formula-by-formula way (no goal splitting/branching)
2. It does not produce multiple goals from one
3. It is a pure simplification (rewrites terms without adding new conjuncts that split the goal)
4. It doesn't require global goal analysis beyond what `dependent_expr_state` provides

A tactic is **not suitable** for conversion if:
- It splits goals into multiple subgoals
- It requires tight coupling to the goal infrastructure
- It depends on features unavailable in `dependent_expr_simplifier` (e.g., `goal_num_occurs`)
- It only makes sense in a tactic pipeline (e.g., `fail`, `skip`, `sat`, `smt`, solver tactics)
- It is a portfolio tactic (combines multiple tactics)

### Step 5: Check for Existing Issues

Before creating any issue, search for existing open issues to avoid duplicates:

Use GitHub tools to search: `repo:${{ github.repository }} is:issue is:open label:tactic-to-simplifier "<tactic-name>"`

Also check cache memory for previously created issues.

### Step 6: Create Issues for Convertible Tactics

For each convertible tactic that does not already have an open issue:

1. Read the tactic's existing implementation carefully (header + cpp files)
2. Design the corresponding `dependent_expr_simplifier` subclass
3. Draft the code for the new simplifier

Use `create-issue` to create a GitHub issue with:

**Title**: `Convert tactic '<tactic-name>' to a simplifier`

**Body**:

```markdown
## Summary

The `<tactic-name>` tactic (described as: "<description>") currently only exists as a `tactic`
and has no corresponding `dependent_expr_simplifier`. This issue proposes converting it to
expose it as both a tactic (via the `dependent_expr_state_tactic` wrapper) and a simplifier.

## Background

Z3 provides two abstraction layers for formula transformation:
- **Tactics** (`tactic` base class): Operate on goals
- **Simplifiers** (`dependent_expr_simplifier` base class): Operate on individual formulas in a `dependent_expr_state`

The modern pattern wraps a simplifier inside a tactic using `dependent_expr_state_tactic`.

## Current Implementation

File: `<path/to/tactic/header.h>`

```cpp
// Existing tactic registration
ADD_TACTIC("<tactic-name>", "<description>", "mk_<tactic_name>_tactic(m, p)")
```

## Proposed Change

### 1. Create a new simplifier class in `src/ast/simplifiers/<name>_simplifier.h`:

```cpp
#pragma once
#include "ast/simplifiers/dependent_expr_state.h"
// ... other includes

class <name>_simplifier : public dependent_expr_simplifier {
    // ... internal state
public:
    <name>_simplifier(ast_manager& m, params_ref const& p, dependent_expr_state& s)
        : dependent_expr_simplifier(m, s) { }

    char const* name() const override { return "<simplifier-name>"; }

    void reduce() override {
        for (unsigned idx : indices()) {
            auto& d = m_fmls[idx];
            // ... transform d.fml() ...
            expr_ref new_fml(m);
            // apply simplification
            m_fmls.update(idx, dependent_expr(m, new_fml, nullptr, d.dep()));
        }
    }
};
```

### 2. Update `<path/to/existing/tactic_header.h>` to add the simplifier registration and new tactic factory:

```cpp
#include "tactic/dependent_expr_state_tactic.h"
#include "ast/simplifiers/<name>_simplifier.h"

inline tactic* mk_<name>2_tactic(ast_manager& m, params_ref const& p = params_ref()) {
    return alloc(dependent_expr_state_tactic, m, p,
        [](auto& m, auto& p, auto& s) -> dependent_expr_simplifier* {
            return alloc(<name>_simplifier, m, p, s);
        });
}

/*
  ADD_TACTIC("<tactic-name>2", "<description>", "mk_<name>2_tactic(m, p)")
  ADD_SIMPLIFIER("<tactic-name>", "<description>", "alloc(<name>_simplifier, m, p, s)")
*/
```

## Benefits

- Enables use of `<tactic-name>` in Z3's simplifier pipeline (used by the new solver engine)
- Follows the established modern pattern for formula simplification in Z3
- No behavioral change for existing tactic users

## Notes

- The original `mk_<tactic_name>_tactic` should remain for backward compatibility
- The simplifier should implement `supports_proofs()` if proof generation is relevant
```

**Important instructions for issue body**:
- Replace all placeholders (`<tactic-name>`, `<name>`, `<description>`, `<path>`, etc.) with **real, specific values** from the actual source code
- Provide **actual code** based on reading the tactic's implementation, not generic templates
- Include the real factory expression, include paths, and class names from the existing implementation
- If the tactic has parameters, include them in the simplifier
- If the tactic wraps another component (rewriter, solver, etc.), include that in the simplifier too

### Step 7: Update Cache Memory

Store in cache memory:
- The list of all tactics analyzed in this run
- The list of issues created (tactic name → issue number)
- Tactics determined to be non-convertible and why
- Tactics with existing issues (to skip in future runs)

## Conversion Criteria Reference

### Likely Convertible (if no simplifier exists)
- Pure term rewriting tactics (apply rewriting rules)
- Bound propagation tactics
- Variable elimination tactics that work formula-by-formula
- Normalization tactics (NNF, SNF) that apply local transformations
- Tactics that simplify based on syntactic structure

### Not Convertible (skip these)
- Solver-based tactics (`ctx-solver-simplify`, `sat`, `smt`, etc.) — require a solver
- Portfolio/combinator tactics (`then`, `or-else`, `repeat`, etc.)
- Decision procedure tactics (`qfbv`, `qflra`, etc.)
- Tactics that split goals (`split-clause`, `tseitin-cnf`, `occf`)
- Tactics that only make sense in goal context (`fail`, `skip`)
- Tactics using `goal_num_occurs` for occurrence counting (the simplifier doesn't have this)
- Tactics that produce multiple result goals

## Guidelines

- **Be specific**: Provide actual file paths, class names, and factory expressions — no generic placeholders
- **Be careful**: Only create issues for tactics that are genuinely good candidates
- **Avoid duplicates**: Always check existing issues before creating new ones
- **One issue per tactic**: Create separate issues for each convertible tactic
- **Read the code**: Examine the actual tactic implementation before proposing code for the simplifier
- **Be incremental**: If there are many candidates, focus on the most impactful ones first
- **Limit per run**: Create at most 3 new issues per run to avoid flooding the issue tracker
