# SpecBot Report: Z3 c3 Branch — Sequence Solver (`src/smt/seq/`)

> **Target module:** `z3-c3/src/smt/seq/`  
> **Repository:** [Z3Prover/z3](https://github.com/Z3Prover/z3) branch `c3` commit `6e8c201`  
> **Files analyzed:** `seq_nielsen.h/cpp`, `seq_state.h/cpp`, `seq_regex.h/cpp`, `seq_parikh.h/cpp`  
> **Date:** 2026-04-02  
> **Methodology:** Runtime-validated — 34 assertions (4 inv + 12 pre + 18 post) instrumented
> into `seq_nielsen.cpp`, rebuilt, and exercised via three test suites:
> 1. **Z3's own tests** (`test-z3.exe`): `nseq_basic` ✅, `seq_regex` ✅, `seq_parikh` ✅, `nseq_zipt` ❌ stack overflow, `seq_nielsen` ❌ assertion violation
> 2. **Specbot co-generated** (`test_specbot_seq.c`): 16 tests (13 pass, 3 crash)
> 3. **DeepTest-generated** (`test_deeptest_seq.c`): 49 tests (36 pass, 13 crash)
>
> **Results:** 34 assertions, ~5,000 checks, **1 suspect** (`post_solve_sat_path_nonempty` 33% pass rate from Z3's own tests), 16 crash-triggering tests, 2 Z3-internal test failures.

---

## 1. Module Overview

The `src/smt/seq/` directory implements a **Nielsen-transformation–based string constraint solver** for Z3, ported from the [ZIPT](https://github.com/CEisenhofer/ZIPT) system. The solver builds a search graph of constraint states connected by substitutions and decides satisfiability of conjunctions of string equalities (`str_eq`) and regex membership constraints (`str_mem`) using depth-bounded DFS with iterative deepening.

### 1.1 Core Classes and Structs

| Class/Struct | File | Description |
|---|---|---|
| `str_eq` | `seq_nielsen.h:368` | String equality constraint `lhs = rhs`. Both sides are `euf::snode*` trees (DAGs of string tokens). Carries a `dep_tracker` for conflict explanation. |
| `str_mem` | `seq_nielsen.h:394` | Regex membership constraint `str ∈ regex`. Carries derivation history (`m_history`) for cycle detection, a unique `m_id`, and `dep_tracker`. |
| `nielsen_subst` | `seq_nielsen.h:423` | Variable substitution `var → replacement`. `m_var` may be `s_var`, `s_power`, or `s_unit`. Carries `dep_tracker`. |
| `char_subst` | `seq_nielsen.h:347` | Character-level substitution mapping a symbolic `s_unit` to a concrete `s_char` or another `s_unit`. |
| `constraint` | `seq_nielsen.h:455` | Integer arithmetic constraint (equality, inequality, or disequality) stored per node. Wraps an `expr_ref` formula and `dep_tracker`. |
| `length_constraint` | `seq_nielsen.h:475` | Arithmetic length constraint derived from string equalities (e.g., `len(lhs) = len(rhs)`). Has a `length_kind` tag. |
| `nielsen_edge` | `seq_nielsen.h:491` | Edge in the Nielsen graph connecting two `nielsen_node`s. Carries substitutions, side constraints, and a progress flag. |
| `nielsen_node` | `seq_nielsen.h:526` | Node in the Nielsen graph. Holds the current constraint set (`str_eq`, `str_mem`, `constraint`), outgoing edges, backtrack state (reason, conflict flags), character constraints, and regex occurrence tracking. |
| `nielsen_graph` | `seq_nielsen.h:749` | The top-level Nielsen transformation graph. Owns all nodes and edges. Manages the search (iterative-deepening DFS), the arithmetic subsolver interface, Parikh filter, regex module, and modification counters. |
| `simple_solver` | `seq_nielsen.h:274` | Abstract interface for an incremental arithmetic subsolver. Provides `check()`, `assert_expr()`, `push()`/`pop()`, and optional bound queries. |
| `nielsen_stats` | `seq_nielsen.h:716` | Accumulated search statistics (solve calls, DFS nodes, modifier counts, etc.). |
| `tracked_str_eq` | `seq_state.h:30` | Extends `str_eq` with SMT-layer `enode*` pair for conflict reporting. |
| `tracked_str_mem` | `seq_state.h:36` | Extends `str_mem` with a `sat::literal` for conflict reporting. |
| `seq_regex` | `seq_regex.h:40` | Regex membership processing: stabilizer store, Brzozowski derivatives, emptiness checks, cycle detection, self-stabilizing propagation. Wraps `euf::sgraph`. |
| `seq_parikh` | `seq_parikh.h:62` | Parikh image filter: computes length stride of regex languages and generates modular arithmetic constraints (`len(str) = min_len + stride·k`). |

### 1.2 Key Relationships

```
nielsen_graph
  ├── owns: ptr_vector<nielsen_node>   (all nodes)
  ├── owns: ptr_vector<nielsen_edge>   (all edges)
  ├── owns: seq_parikh*                (Parikh filter)
  ├── owns: seq_regex*                 (regex module)
  ├── refs: simple_solver& m_solver    (arithmetic subsolver, not owned)
  ├── refs: simple_solver& m_core_solver
  ├── refs: euf::sgraph& m_sg          (string graph, not owned)
  └── refs: seq_util& m_seq

nielsen_node
  ├── refs: nielsen_graph& m_graph     (back-pointer to owning graph)
  ├── has: vector<str_eq>              (string equalities)
  ├── has: vector<str_mem>             (regex memberships)
  ├── has: vector<constraint>          (integer constraints)
  ├── has: ptr_vector<nielsen_edge>    (outgoing edges, not owned)
  └── refs: nielsen_node* m_backedge   (optional back-edge for cycle)

nielsen_edge
  ├── refs: nielsen_node* m_src        (source node, not owned)
  ├── refs: nielsen_node* m_tgt        (target node, not owned)
  ├── has: vector<nielsen_subst>       (substitutions)
  └── has: vector<constraint>          (side constraints)

seq_regex
  ├── refs: euf::sgraph& m_sg
  ├── has: u_map<ptr_vector<snode>> m_stabilizers
  └── has: uint_set m_self_stabilizing

seq_parikh
  ├── refs: ast_manager& m
  ├── has: seq_util, arith_util
  └── has: unsigned m_fresh_cnt
```

### 1.3 Enum Types

| Enum | Values | Description |
|---|---|---|
| `simplify_result` | `proceed`, `conflict`, `satisfied`, `restart`, `restart_and_satisfied` | Outcome of constraint simplification at a node. |
| `backtrack_reason` | `unevaluated`, `extended`, `symbol_clash`, `parikh_image`, `subsumption`, `arithmetic`, `regex`, `regex_widening`, `character_range`, `smt`, `external`, `children_failed` | Why a node was backtracked from. |
| `search_result` | `sat`, `unsat`, `unknown` | Outcome of solve()/search_dfs(). |
| `length_kind` | `nonneg`, `eq`, `bound` | Type of arithmetic length constraint. |

---

## 2. Specification Catalog

All specifications are runtime-validated. Checks column shows Z3 tests / Specbot / DeepTest / Total.

### Suspect

| ID | Kind | Scope | Expression | Z3 | Specbot | DeepTest | Total | Pass Rate |
|---|---|---|---|---|---|---|---|---|
| `post_solve_sat_path_nonempty` | post | `nielsen_graph::solve()` → SAT | `!m_sat_path.empty()` | **1/3** | 5 | 15 | 21/23 | **91%** |

Z3's `nseq_basic` test triggers SAT results where `m_sat_path` is empty — the solver returns SAT but doesn't populate the solution path. This may indicate a code path where `solve()` returns SAT via simplification (root satisfied without search) rather than DFS, skipping path construction.

### 2.1 `str_eq`

| ID | Kind | Scope | Expression | Z3 | Specbot | DeepTest | Total |
|---|---|---|---|---|---|---|---|
| `inv_eq_nonnull` | inv | `str_eq` (all public methods) | `[&]{ for (auto const& eq : m_str_eq) if (!eq.m_lhs \|\| !eq.m_rhs) return false; return true; }()` | 8 | 16 | 114 | 138 |
| `inv_no_trivial_eq` | inv | `str_eq` (after simplify) | `[&]{ for (auto const& eq : m_str_eq) if (eq.m_lhs == eq.m_rhs && eq.m_lhs != nullptr) return false; return true; }()` | 5 | 16 | 106 | 127 |
| `post_sort_ordered` | post | `str_eq::sort()` | `m_lhs->id() <= m_rhs->id()` | 7 | 34 | 303 | 344 |

### 2.2 `str_mem`

| ID | Kind | Scope | Expression | Z3 | Specbot | DeepTest | Total |
|---|---|---|---|---|---|---|---|
| `pre_add_mem_str_nonnull` | pre | `nielsen_node::add_str_mem()` | `mem.m_str != nullptr` | 2 | 7 | 63 | 72 |
| `pre_add_mem_regex_nonnull` | pre | `nielsen_node::add_str_mem()` | `mem.m_regex != nullptr` | 2 | 7 | 63 | 72 |

### 2.3 `nielsen_subst`

| ID | Kind | Scope | Expression | Z3 | Specbot | DeepTest | Total |
|---|---|---|---|---|---|---|---|
| `pre_apply_subst_var_nonnull` | pre | `nielsen_node::apply_subst()` | `s.m_var != nullptr` | 1 | 23 | 148 | 172 |
| `pre_apply_subst_repl_nonnull` | pre | `nielsen_node::apply_subst()` | `s.m_replacement != nullptr` | 1 | 23 | 148 | 172 |

### 2.4 `nielsen_edge`

| ID | Kind | Scope | Expression | Z3 | Specbot | DeepTest | Total |
|---|---|---|---|---|---|---|---|
| `pre_mk_edge_src_nonnull` | pre | `nielsen_graph::mk_edge()` | `src != nullptr` | 1 | 20 | 146 | 167 |
| `pre_mk_edge_tgt_nonnull` | pre | `nielsen_graph::mk_edge()` | `tgt != nullptr` | 1 | 20 | 146 | 167 |

### 2.5 `nielsen_node`

| ID | Kind | Scope | Expression | Z3 | Specbot | DeepTest | Total |
|---|---|---|---|---|---|---|---|
| `pre_add_eq_lhs_nonnull` | pre | `nielsen_node::add_str_eq()` | `eq.m_lhs != nullptr` | 7 | 12 | 117 | 136 |
| `pre_add_eq_rhs_nonnull` | pre | `nielsen_node::add_str_eq()` | `eq.m_rhs != nullptr` | 7 | 12 | 117 | 136 |
| `pre_clone_from_valid` | pre | `nielsen_node::clone_from()` | `parent.m_id != UINT_MAX` | 1 | 20 | 146 | 167 |
| `post_clone_str_eq_count` | post | `nielsen_node::clone_from()` | `m_str_eq.size() == parent.m_str_eq.size()` | 1 | 20 | 146 | 167 |
| `post_clone_str_mem_count` | post | `nielsen_node::clone_from()` | `m_str_mem.size() == parent.m_str_mem.size()` | 1 | 20 | 146 | 167 |
| `post_clone_constraint_count` | post | `nielsen_node::clone_from()` | `m_constraints.size() == parent.m_constraints.size()` | 1 | 20 | 146 | 167 |
| `pre_gen_ext_node_nonnull` | pre | `nielsen_graph::generate_extensions()` | `node != nullptr` | 1 | 11 | 89 | 101 |
| `pre_gen_ext_node_not_conflict` | pre | `nielsen_graph::generate_extensions()` | `!node->is_currently_conflict()` | 1 | 11 | 89 | 101 |
| `post_simplify_sat_no_eq` | post | `nielsen_node::simplify_and_init()` | `m_str_eq.empty()` (on satisfied) | 4 | 5 | 15 | 24 |
| `post_simplify_sat_no_mem` | post | `nielsen_node::simplify_and_init()` | `m_str_mem.empty()` (on satisfied) | 4 | 5 | 15 | 24 |
| `post_simplify_conflict_flagged` | post | `nielsen_node::simplify_and_init()` | `is_currently_conflict()` (on conflict) | 3 | 0 | 7 | 10 |

### 2.6 `nielsen_graph`

| ID | Kind | Scope | Expression | Z3 | Specbot | DeepTest | Total |
|---|---|---|---|---|---|---|---|
| `inv_root_consistent` | inv | `nielsen_graph` (all public methods) | `m_root == nullptr \|\| std::find(m_nodes.begin(), m_nodes.end(), m_root) != m_nodes.end()` | 6 | 8 | 29 | 43 |
| `inv_node_id_sequential` | inv | `nielsen_graph` (all public methods) | `[&]{ for (unsigned i = 0; i < m_nodes.size(); ++i) if (m_nodes[i]->id() != i) return false; return true; }()` | 6 | 8 | 29 | 43 |
| `pre_solve_root_exists` | pre | `nielsen_graph::solve()` | `m_root != nullptr` | 6 | 8 | 29 | 43 |
| `post_solve_sat_has_node` | post | `nielsen_graph::solve()` → SAT | `m_sat_node != nullptr` | 3 | 5 | 15 | 23 |
| `post_solve_unsat_has_conflict` | post | `nielsen_graph::solve()` → UNSAT | `!m_conflict_sources.empty()` | 3 | 0 | 0 | 3 |
| `post_create_root_set` | post | `nielsen_graph::create_root()` | `m_root != nullptr` | 9 | 40 | 152 | 201 |
| `post_create_root_id_zero` | post | `nielsen_graph::create_root()` | `m_root->id() == 0` | 9 | 40 | 152 | 201 |
| `post_create_root_in_nodes` | post | `nielsen_graph::create_root()` | `m_nodes[0] == m_root` | 9 | 40 | 152 | 201 |
| `post_mk_node_id_matches` | post | `nielsen_graph::mk_node()` | `n->id() == m_nodes.size() - 1` | 11 | 60 | 298 | 369 |
| `post_mk_node_in_nodes` | post | `nielsen_graph::mk_node()` | `m_nodes.back() == n` | 11 | 60 | 298 | 369 |
| `post_reset_nodes_empty` | post | `nielsen_graph::reset()` | `m_nodes.empty()` | 12 | 49 | 168 | 229 |
| `post_reset_edges_empty` | post | `nielsen_graph::reset()` | `m_edges.empty()` | 12 | 49 | 168 | 229 |
| `post_reset_root_null` | post | `nielsen_graph::reset()` | `m_root == nullptr` | 12 | 49 | 168 | 229 |
| `post_reset_sat_null` | post | `nielsen_graph::reset()` | `m_sat_node == nullptr` | 12 | 49 | 168 | 229 |


## 3. Confirmed Crashes and Failures

### Z3's own test failures (2)

**`nseq_zipt`** — Stack overflow (exit code `0xC00000FD`) after 88 seconds on equation `aaX = Xa`
```
test_zipt_str_equations:
Checking equation: aaX = Xa   ← hangs here, then stack overflow
```

**`seq_nielsen`** — Assertion violation: `root->outgoing().size() == 3` at `seq_nielsen.cpp:514`
```
test_eq_split_basic
ASSERTION VIOLATION
File: C:\Users\Shuvendu\z3-c3\src\test\seq_nielsen.cpp
Line: 514
root->outgoing().size() == 3
```

### Specbot + DeepTest crash-triggering tests (16)

16 additional tests crash Z3 on pre-existing hard SASSERTs (3 specbot, 13 DeepTest).

All tests use the Z3 C API with `smt.string_solver=nseq`.

- Specbot tests: `C:\Users\Shuvendu\z3-c3\build_nokiad\test_specbot_seq.c`
- DeepTest tests: `C:\Users\Shuvendu\z3-c3\build_nokiad\test_deeptest_seq.c`

### Crash sites

| Crash site | Root cause |
|-----------|-----------|
| `seq_nielsen.cpp:~3604` | Hard SASSERT `n->is_currently_conflict()` — node conflict state inconsistency |
| `seq_nielsen.h:649` | Backtrack reason state bug |
| `seq_nielsen.h:434` | Variable classification bug (`seq_extract`) |
| `seq_nielsen.cpp:3933` | Unexpected SAT on sub-check (`contains`) |

### Specbot co-generated tests (3 crashes)

**`test_regex_combined`** — `x ∈ [0-9]+` combined with `x ++ "-" ++ y = "123-abc"` *(specbot)*
```c
Z3_solver_assert(ctx, s, Z3_mk_seq_in_re(ctx, x, Z3_mk_re_plus(ctx, Z3_mk_re_range(ctx, "0", "9"))));
Z3_solver_assert(ctx, s, Z3_mk_eq(ctx, mk_concat(ctx, x, mk_concat(ctx, "-", y)), "123-abc"));
```

**`test_quadratic_eq`** — `x ++ x = y ++ y` *(specbot)*
```c
Z3_solver_assert(ctx, s, Z3_mk_eq(ctx, mk_concat(ctx, x, x), mk_concat(ctx, y, y)));
```

**`test_long_string_eq`** — `x ++ y = "aaa...a"` (100 chars) with `|x| = 50` *(specbot)*
```c
Z3_solver_assert(ctx, s, Z3_mk_eq(ctx, mk_concat(ctx, x, y), "aaa...a" /* 100 'a's */));
Z3_solver_assert(ctx, s, Z3_mk_eq(ctx, Z3_mk_seq_length(ctx, x), 50));
```

### DeepTest-generated tests — quadratic/power equations (5 crashes)

**`test_commutative_eq`** — `x ++ y = y ++ x` with `|x|=2, |y|=3` *(DeepTest)*
```c
Z3_solver_assert(ctx, s, Z3_mk_eq(ctx, mk_cat(ctx, x, y), mk_cat(ctx, y, x)));
Z3_solver_assert(ctx, s, Z3_mk_eq(ctx, mk_len(ctx, x), mk_int(ctx, 2)));
Z3_solver_assert(ctx, s, Z3_mk_eq(ctx, mk_len(ctx, y), mk_int(ctx, 3)));
```

**`test_triple_double`** — `x ++ x ++ x = y ++ y` with `|x|=2` *(DeepTest)*
```c
Z3_solver_assert(ctx, s, Z3_mk_eq(ctx, mk_cat3(ctx, x, x, x), mk_cat(ctx, y, y)));
Z3_solver_assert(ctx, s, Z3_mk_eq(ctx, mk_len(ctx, x), mk_int(ctx, 2)));
```

**`test_power_eq`** — `x ++ x = "abab"` *(DeepTest)*
```c
Z3_solver_assert(ctx, s, Z3_mk_eq(ctx, mk_cat(ctx, x, x), mk_str(ctx, "abab")));
```

**`test_power_four_repeat`** — `x⁴ = "abcdabcdabcdabcd"` *(DeepTest)*
```c
Z3_ast x4 = mk_cat(ctx, mk_cat(ctx, x, x), mk_cat(ctx, x, x));
Z3_solver_assert(ctx, s, Z3_mk_eq(ctx, x4, mk_str(ctx, "abcdabcdabcdabcd")));
```

**`test_quadratic_interleaved`** — `x ++ "a" ++ y = y ++ "a" ++ x` with `|x|=1, |y|=1` *(DeepTest)*
```c
Z3_solver_assert(ctx, s, Z3_mk_eq(ctx, mk_cat3(ctx, x, a, y), mk_cat3(ctx, y, a, x)));
Z3_solver_assert(ctx, s, Z3_mk_eq(ctx, mk_len(ctx, x), mk_int(ctx, 1)));
Z3_solver_assert(ctx, s, Z3_mk_eq(ctx, mk_len(ctx, y), mk_int(ctx, 1)));
```

### DeepTest-generated tests — deep variable chains (3 crashes)

**`test_deep_chain_10`** — 10-variable cascade with length constraint *(DeepTest)*
```c
// v0++v1=v2, v2++v3=v4, v4++v5=v6, v6++v7=v8, v8++v9=v10
// v10 = "abcdefghij", |v0| = 1
```

**`test_diamond_subst`** — diamond: `x++y=z, x++w=z, z="abcdef", |x|=2` *(DeepTest)*
```c
Z3_solver_assert(ctx, s, Z3_mk_eq(ctx, mk_cat(ctx, x, y), z));
Z3_solver_assert(ctx, s, Z3_mk_eq(ctx, mk_cat(ctx, x, w), z));
Z3_solver_assert(ctx, s, Z3_mk_eq(ctx, z, mk_str(ctx, "abcdef")));
Z3_solver_assert(ctx, s, Z3_mk_eq(ctx, mk_len(ctx, x), mk_int(ctx, 2)));
```

**`test_wide_fan`** — `x = a0++a1++a2++a3++a4` with all `|ai|=2`, `x="aabbccddee"` *(DeepTest)*

### DeepTest-generated tests — regex + equations (1 crash)

**`test_regex_plus_eq`** — `x ∈ [a-z]{3}` combined with `x++y = "abcdef"` *(DeepTest)*
```c
Z3_solver_assert(ctx, s, Z3_mk_seq_in_re(ctx, x, Z3_mk_re_loop(ctx, mk_range(ctx, "a", "z"), 3, 3)));
Z3_solver_assert(ctx, s, Z3_mk_eq(ctx, mk_cat(ctx, x, y), mk_str(ctx, "abcdef")));
```

### DeepTest-generated tests — incremental solving (2 crashes)

**`test_incremental_concat_varying`** — 30 push/pop rounds with varying concat targets *(DeepTest)*

**`test_incremental_nested`** — 10×5 nested push/pop with length constraints *(DeepTest)*

### DeepTest-generated tests — string operations (2 crashes)

**`test_substr_extract`** — `substr(x,1,3) = "ell"` with prefix "h" and `|x|=5` *(DeepTest)*
```c
Z3_solver_assert(ctx, s, Z3_mk_eq(ctx, Z3_mk_seq_extract(ctx, x, 1, 3), mk_str(ctx, "ell")));
Z3_solver_assert(ctx, s, Z3_mk_seq_prefix(ctx, mk_str(ctx, "h"), x));
Z3_solver_assert(ctx, s, Z3_mk_eq(ctx, mk_len(ctx, x), mk_int(ctx, 5)));
```

**`test_indexof_constraint`** — `indexof(x, "bc", 0) = 1` with `|x|=5` *(DeepTest)*
```c
Z3_solver_assert(ctx, s, Z3_mk_eq(ctx, Z3_mk_seq_index(ctx, x, mk_str(ctx,"bc"), 0), mk_int(ctx, 1)));
Z3_solver_assert(ctx, s, Z3_mk_eq(ctx, mk_len(ctx, x), mk_int(ctx, 5)));
```

---

## 4. Configuration

```
spec_mode:          all
use_spec_db:        false
use_deeptest_tests: true (49 DeepTest tests generated)
run_mutation:        false
refinements:         3
```

---

*End of SpecBot Report*
