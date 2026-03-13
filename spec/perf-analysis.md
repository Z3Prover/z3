# Analysis Report: theory_nseq Improvements Based on ZIPT

## Overview

We profiled 3 benchmarks where `theory_nseq` performs worse than both `theory_seq` and ZIPT,
representing the two distinct failure modes observed across the full 54-benchmark suite.

**Profiled benchmarks:**

| Benchmark | seq | nseq | ZIPT | Failure Mode |
|-----------|-----|------|------|--------------|
| automatark-lu/instance00000.smt2 | sat (0.32s) | timeout (10s) | sat (fast) | DFS explosion |
| queries/query2885.smt2 | sat (3.1s) | unknown (0.15s) | sat (fast) | Incomplete — gives up |
| hornstr-equiv/Burns_lstar.smt2 | sat (0.38s) | unknown (0.06s) | sat (fast) | Incomplete — gives up |

Trace files are saved in `spec/traces/`:
- `nseq_automatark_trace.log`, `seq_automatark_trace.log`, `zipt_automatark.log`
- `nseq_query2885_trace.log`, `seq_query2885_trace.log`, `zipt_query2885.log`
- `nseq_burns_trace.log`, `seq_burns_trace.log`, `zipt_burns.log`

---

## Failure Mode 1: DFS Explosion on Regex Bounded Repetitions

**Affected:** automatark-lu benchmarks (3/54), PCP benchmarks (6/54)

### Problem

The automatark benchmark asserts `not (str.in_re X R)` where R uses `(_ re.loop 2 2)`,
`(_ re.loop 4 4)`, and `(_ re.loop 22 22)` over digit ranges. nseq converts this to
membership in `complement(R)` and attempts DFS solving.

**nseq statistics:**
```
nseq-dfs-nodes      52,696,075    ← 52M nodes explored before timeout
nseq-final-checks   1
nseq-solve-calls    1
```

The iterative-deepening DFS in `seq_nielsen.cpp` branches on every character position
using `apply_regex_var_split`, which generates branches for each minterm of the regex
derivative. For bounded repetitions like `(_ re.loop 4 4) (re.range "0" "9")`, this
creates 10 branches per position × 4 positions = 10,000+ paths per loop, and the
benchmark has 5 such loops plus a 22-character alternative.

### How seq solves it (0.32s)

theory_seq uses axiom-based regex unfolding via `seq_regex::propagate_in_re`:
- Converts `str.in_re` to `aut.accept` predicates
- Unfolds one character at a time using derivative axioms
- Relies on CDCL(T) conflict-driven learning to prune the search space
- Statistics: 79 axioms, 21 reductions, 9 conflicts, 5 final-checks

### How ZIPT solves it (fast)

ZIPT evaluates the regex membership constraint directly at the Boolean level:
```
Fixed (reMember X!0 (concat ...)): False    ← membership determined in one step
```
ZIPT propagates the Boolean value of `str.in_re` as a fixed assignment, then
finds a satisfying assignment for X (empty string works since the constraint is negated).
No character-by-character enumeration needed.

### Recommendation

1. **Add regex membership pre-evaluation**: Before DFS, check if the regex membership
   can be evaluated directly (e.g., by finding a witness string using BFS on the regex
   automaton, or checking if empty string satisfies). This is what ZIPT does.

2. **Add DFS node budget with fallback**: When `nseq-dfs-nodes` exceeds a threshold
   (e.g., 1M), abandon DFS and fall back to axiom-based unfolding. Currently nseq
   runs until timeout.

3. **Optimize bounded repetition handling**: For `(_ re.loop n n) R`, expand to
   length constraint `len(s) = n` + character membership constraints rather than
   branching on all `|R|^n` possibilities.

---

## Failure Mode 2: Incomplete — Gives Up on Complex Regex Memberships

**Affected:** queries (8/54), hornstr-equiv (1/54), slog (1/54), matching (1/54)

### Problem

nseq explores only 1 DFS node and returns `unknown` for benchmarks with complex regex
membership constraints. The trace shows:

**query2885 (Boolean combination of regex memberships):**
```
nseq populate: 0 eqs, 3 mems -> nielsen root with 0 eqs, 3 mems
nseq length lemma: (>= (str.len x) 6)
nseq length propagation: (>= (str.len x) 6)
Could not match (RegEx String) and (Seq k!0)    ← sort mismatch, processing stops
```

**Burns (multiple variables with regex + equality):**
```
nseq populate: 0 eqs, 4 mems -> nielsen root with 0 eqs, 4 mems
nseq length lemma: (>= (str.len varin) 2)
Could not match (RegEx String) and (Seq k!0)    ← same issue
```

nseq has **0 word equations** and only regex membership constraints. After adding one
length lemma, the DFS finds a single node with no applicable modifiers and gives up.

The `"Could not match (RegEx String) and (Seq k!0)"` message from `seq_decl_plugin.cpp:74`
indicates a sort-unification failure when nseq tries to process regex constraints through
generic sequence operations. This suggests the regex-to-Nielsen integration has gaps.

### How seq solves these

theory_seq uses `seq_regex::propagate_in_re` → `aut.accept` axioms → derivative unfolding:

**query2885:** 1303 axioms, 1162 reductions → sat in 3.1s
**Burns:** 121 axioms, 22 reductions → sat in 0.38s

The axiom-based approach systematically unfolds regex memberships through the CDCL(T)
framework, generating constraints one character position at a time.

### How ZIPT solves these

ZIPT evaluates multiple regex memberships and propagates their Boolean values:

**query2885:**
```
Fixed (reMember x!0 ...): False     ← first membership
Fixed (reMember x!0 ...): True      ← second membership
Fixed (reMember x!0 ...): False     ← third membership
→ SAT (model: x = "\x00\x00\x00ACA")
```

**Burns:**
```
Fixed (reMember varout!0 ...): True
Fixed (reMember varin!13 ...): True
Fixed (reMember varin!13 ...): True   ← second membership on varin
Fixed (reMember varin!13 ...): True   ← third membership on varin
→ SAT (model: varin = "66", varout = "")
```

ZIPT's key advantage: it evaluates regex membership as a **Boolean decision** using
direct automata/derivative evaluation, and uses Decide/Push for SAT search. It doesn't
attempt to enumerate string characters one-by-one through DFS.

### Recommendation

1. **Implement regex membership evaluation via automata**: When nseq encounters
   `str.in_re(s, R)` with no word equations, build a small automaton for R and check
   satisfiability directly. If sat, extract a witness string. This is ZIPT's core approach.

2. **Handle multiple memberships via product construction**: For problems like Burns
   with multiple `str.in_re` on the same variable, compute the intersection automaton
   and check emptiness. ZIPT does this implicitly.

3. **Fix the sort-matching issue**: The `"Could not match (RegEx String) and (Seq k!0)"`
   error in `seq_decl_plugin.cpp:74` causes nseq to bail out early. This should be
   investigated as a potential bug in how nseq constructs terms during regex processing.

4. **Add Boolean-level regex propagation**: Like ZIPT's "Fixed" mechanism, when a regex
   membership's truth value can be determined (e.g., by finding a satisfying/violating
   string), propagate it as a Boolean assignment rather than trying to encode it in the
   Nielsen graph.

---

## Summary: What theory_nseq Needs from ZIPT

| ZIPT Capability | nseq Status | Priority |
|-----------------|-------------|----------|
| Direct regex membership evaluation (automaton-based) | Missing — nseq uses DFS character enumeration | **High** |
| Boolean-level regex propagation (Fixed/Decide) | Missing — nseq tries to encode in Nielsen graph | **High** |
| Multi-membership intersection | Missing — gives up with 1 DFS node | **High** |
| Bounded repetition optimization | Missing — causes 52M-node DFS explosion | **Medium** |
| DFS node budget / fallback | Missing — runs to timeout | **Medium** |
| Sort-matching fix for regex terms | Bug — `Could not match` error | **Medium** |

### Priority Implementation Order

1. **Regex membership evaluation** — Direct automaton-based satisfiability check for
   `str.in_re` constraints. This single change would fix both failure modes: the DFS
   explosion (by avoiding DFS entirely for regex-only problems) and the incompleteness
   (by providing an alternative solving path when DFS gives up).

2. **Boolean-level propagation** — When regex membership is determined, propagate the
   result as a Boolean literal rather than encoding in the Nielsen graph. This matches
   ZIPT's architecture and works well with the CDCL(T) framework.

3. **DFS budget with axiom fallback** — For cases where DFS is still used, add a node
   budget and fall back to seq-style axiom unfolding when exceeded.

---

## Additional Findings

### Potential Soundness Bug

Benchmark #12 (`dining-cryptographers_sat_non_incre_equiv_init_0_3.smt2`):
- seq = **sat**, nseq = **unsat**, ZIPT = **sat**
- nseq reports unsat while the other two agree on sat. This should be investigated
  as a potential soundness bug in theory_nseq.

### nseq Strengths

nseq excels on word equation problems (track02, track03) and string disequality
(negated-predicates/diseq), solving 6 benchmarks that seq times out on. The Nielsen
transformation approach is fundamentally stronger for these constraint classes.

### Overall Statistics

- **Solved**: seq=30, nseq=22, ZIPT=35 (of 54)
- The 13-benchmark gap between nseq and ZIPT is almost entirely due to regex membership
  handling (10 benchmarks from queries/hornstr-equiv/slog categories).
