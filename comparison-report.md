# Comparison Report: Case Splits in `smt_parallel.cpp` vs. AriParti

## Overview

This report compares how **Z3's `src/smt/smt_parallel.cpp`** and **AriParti** (`src/partitioner/src/math/subpaving/subpaving_t_def.h` + orchestrated by `src/AriParti.py`) perform case splits in parallel arithmetic SMT solving.

---

## Architecture

| Aspect | Z3 `smt_parallel.cpp` | AriParti |
|---|---|---|
| Parallelism model | Shared-memory multi-threaded (C++ threads, one `smt::context` per worker) | Process-based distributed (partitioner process + N solver sub-processes, IPC via named pipes) |
| Where splits happen | Inside each SMT worker thread, using the live SMT context state | In a standalone subpaving partitioner process, before handing off to external solvers |
| Split representation | `expr_ref` atom (e.g., `x ≤ mid`) passed to `batch_manager`, which builds a search tree | Bound pair (`x ≤ mid` / `x > mid`) installed on two child nodes in the subpaving tree |
| Sub-problem dispatch | Workers pull cubes from a shared `search_tree` via `batch_manager::get_cube()` | Child nodes are serialised to `.smt2` files and dispatched to external solver processes |

---

## Case Split Flow

### Z3 (`smt_parallel.cpp`)

```
worker::run()
  → check_cube()     [run SMT check with current cube]
  → l_undef result
  → get_split_atom()
      1. get_arith_split_atom()   ← AriParti-style arithmetic split
      2. VSIDS Boolean fallback   ← if no arithmetic atom found
  → batch_manager::split()        ← insert atom into search tree (binary split)
  → simplify()                    ← optional inprocessing
```

### AriParti (`subpaving_t_def.h` / `AriParti.py`)

```
context_t::operator()()           ← main partitioner loop
  → create_new_task()             ← if a leaf is ready, emit it as an .smt2 task
  → select_split_node()           ← pick highest-priority leaf from heap
  → split_node(n)
      → select_best_var(n)        ← multi-key heuristic
      → compute midpoint
      → mk_node(left), mk_node(right)
      → propagate(left/right)     ← BICP immediately
      → emit "unsat-task" or "new-task" messages to master
```

---

## Variable Selection Heuristic

### Z3 `get_arith_split_atom()`

Iterates over all 0-arity arithmetic enodes visible in the current SMT context. For each variable it records:

- `occ`: count of arithmetic-comparison parent enodes (≤, ≥, <, >, =)
- `has_lo`, `has_up`, `lo`, `up`: current theory bounds from `arith_value`

**Ranking (highest priority first):**
1. **Higher occurrence count** – more active in constraint network
2. **Fully bounded preferred over half-bounded or unbounded**
3. **Wider interval** (for fully-bounded variables)
4. **Interval contains zero** – as tiebreaker

Variables whose interval is already a point (`lo == up`) are skipped.

### AriParti `select_best_var()`

Uses a `var_info` struct with five keys and a *dynamic key ordering* (`key_rank`) that rotates per node to break ties diversely:

| Key index | Criterion | Better is… |
|---|---|---|
| 0 | `m_split_cnt` – global split count | Lower (less-split variables preferred) |
| 1 | `m_cz` – interval contains zero | `true` preferred |
| 2 | `m_deg` – max polynomial degree | Higher preferred (prioritises nonlinear vars) |
| 3 | `m_occ` – occurrence in undecided clauses | Higher preferred |
| 4 | `m_width` – interval width (with penalties for unbounded) | Wider preferred |

Key ordering for a child node is derived from its parent's `key_rank` by rotating one position whenever the parent's ranking had consecutive equal keys; this diversifies splits across the tree.

Variables that are fully determined (`lower == upper`), Boolean (`m_is_bool`), or defined (`m_defs[x] != nullptr`) are excluded.

**Unbounded width penalties (AriParti only):**
- Fully unbounded: `width = 1024²`
- Half-bounded (`(-∞, u]`): `width = 1024 + u` (if `u ≥ 0`), or `width = 1024 / max(1, -u)` (if `u < 0`)
- Half-bounded (`[l, ∞)`): symmetric formula

---

## Midpoint Computation

Both implementations agree on the core zero-split heuristic (AriParti Section 4.2): **if the interval straddles zero, split at 0**.

| Case | Z3 `get_arith_split_atom()` | AriParti `split_node()` |
|---|---|---|
| Interval contains 0 | `mid = 0` | `mid = 0` |
| Fully bounded `[lo, up]` | `mid = (lo + up) / 2`; `floor(mid)` for integers | `mid = (lo + up) / 2`; ceiling applied if `width > 10` |
| Half-bounded `[lo, ∞)` | `mid = lo` (split at lower bound) | `mid = lo + delta` (`delta = 128`) |
| Half-bounded `(-∞, up]` | `mid = up - 1` (int) or `up - 0.5` (real) | `mid = floor(up) - delta` |
| Fully unbounded | `mid = 0` | `mid = 0` (via `m_cz = true`) |

The split produces two branches: `x ≤ mid` and `x > mid` in both cases.

---

## Node / Leaf Selection

### Z3

Workers call `batch_manager::get_cube()`, which calls `search_tree::activate_node()` and `find_active_node()`. The search tree uses a simple work-stealing model: each worker tries to continue the node it last worked on; if unavailable, it picks any open node. There is no explicit priority between open nodes.

### AriParti

Uses a **priority heap** (`m_leaf_heap`, ordered by `node_info::operator<`):

1. **Lowest depth first** – broader, shallower problems are split first
2. **Most undecided clauses** – more constrained nodes processed first
3. **Most undecided literals**
4. **Lowest node ID** (earlier-created nodes preferred as tiebreaker)

This gives AriParti more control over the shape of the partitioning tree.

---

## Post-Split Processing

| Aspect | Z3 | AriParti |
|---|---|---|
| Bound propagation after split | None immediately; full SMT check on next `check_cube()` | Immediate BICP (`propagate()`) on both children; inconsistent children are pruned at once |
| Inprocessing simplification | Optional `simplify()` after split (configurable, one-shot) | None; each sub-task is a fresh SMT instance |
| Learned clause sharing | Yes: units and clauses shared via `batch_manager::collect_clause()` | None: each solver instance is independent |
| Backtracking | `batch_manager::backtrack()` annotates nodes in search tree with unsat-cores | Master (`AriParti.py`) propagates `unsat` upward and downward via `push_up` / `push_down` |

---

## Boolean Variables

- **Z3**: When `get_arith_split_atom()` finds no arithmetic variable, it falls back to a VSIDS-style Boolean heuristic: selects the unassigned Boolean variable with the highest product of positive/negative literal activity scores (`m_lit_scores[0][v] * m_lit_scores[1][v]`), then halves both scores.
- **AriParti**: `select_best_var()` explicitly skips Boolean variables (`if (m_is_bool[x]) continue`). Boolean case splits are not performed by the partitioner; they occur only inside each external solver instance.

---

## Shared Origins and Similarities

Both implementations are directly inspired by the AriParti paper (Section 4.2):

1. **Zero-split heuristic**: both preferentially split at 0 when the interval straddles zero.
2. **Midpoint bisection**: both use `(lo + up) / 2` for fully-bounded intervals.
3. **Occurrence count**: both use the number of arithmetic constraints that mention a variable as a key factor.
4. **Interval width**: both prefer variables with wider intervals as a heuristic for "less constrained" variables.
5. **Binary tree structure**: both build a binary case-split tree where each split adds exactly two child nodes.
6. **Arithmetic-only primary heuristic**: both focus exclusively on arithmetic (Int/Real) variables for the primary split decision.

The Z3 implementation (`get_arith_split_atom()`) was explicitly added to `smt_parallel.cpp` as an "AriParti-style arithmetic interval split" (see comment at line 543–549), making it a direct re-implementation of the core idea from the AriParti paper within Z3's parallel SMT framework.

---

## Key Differences Summary

| Dimension | Z3 `smt_parallel.cpp` | AriParti |
|---|---|---|
| **Architecture** | Shared-memory threads inside Z3 | Distributed processes with IPC |
| **Variable selection keys** | 3 (occ, width, cz) | 5 (split\_cnt, cz, deg, occ, width) with dynamic ordering |
| **Split-count tracking** | Not tracked | Tracked globally; fewer-split vars preferred |
| **Polynomial degree** | Not considered | Considered (key 2: higher degree preferred) |
| **Boolean fallback** | VSIDS-style score-based | None (Boolean vars skipped entirely) |
| **Unbounded width** | Sentinel `−1`; fully-bounded strictly preferred | Penalty values (1024, 1024²) enable ranking across all cases |
| **Split delta (semi-unbounded)** | `1` (int) / `0.5` (real) | `128` (fixed `m_split_delta`) |
| **Node priority** | Work-stealing, no explicit ordering | Priority heap (depth, undecided clauses, undecided literals) |
| **Post-split propagation** | None until full SMT check | Immediate BICP; infeasible children pruned instantly |
| **Clause learning across workers** | Yes (shared via batch\_manager) | No (each solver is isolated) |
| **Inprocessing** | Optional (`m_inprocessing` flag) | None (whole new sub-task per child) |
| **SLS portfolio** | Yes (optional parallel SLS worker) | No |

---

## Source Locations

| Component | File |
|---|---|
| Z3 arithmetic split | `src/smt/smt_parallel.cpp`, `worker::get_arith_split_atom()` (lines 414–534) |
| Z3 Boolean split fallback | `src/smt/smt_parallel.cpp`, `worker::get_split_atom()` (lines 537–570) |
| Z3 search tree split | `src/smt/smt_parallel.cpp`, `batch_manager::split()` (lines 342–358) |
| AriParti variable selection | `src/partitioner/src/math/subpaving/subpaving_t_def.h`, `select_best_var()` (lines 2354–2421) |
| AriParti var\_info ranking | `src/partitioner/src/math/subpaving/subpaving_t.h`, `struct var_info`, `operator<` (lines 453–519) |
| AriParti split\_node | `src/partitioner/src/math/subpaving/subpaving_t_def.h`, `split_node()` (lines 2516–2610) |
| AriParti node priority | `src/partitioner/src/math/subpaving/subpaving_t.h`, `struct node_info`, `operator<` (lines 430–451) |
| AriParti master orchestration | `src/AriParti.py`, `ArithPartition::solve()` and `push_up()` / `push_down()` |
