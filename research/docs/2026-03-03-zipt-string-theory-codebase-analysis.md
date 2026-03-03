---
date: 2026-03-03 20:46:00 UTC
researcher: Copilot CLI
git_commit: fb674ac5b2e722dfe1086c7d952054a0bc11c963
branch: c3
repository: c3
topic: "ZIPT-related string theory components: sgraph, seq_plugin, Nielsen graphs, theory_seq, seq_rewriter, axioms"
tags: [research, codebase, zipt, sgraph, seq_plugin, nielsen, theory_seq, seq_rewriter, seq_axioms, seq_decl_plugin, strings, regex]
status: complete
last_updated: 2026-03-03
last_updated_by: Copilot CLI
---

# Research: ZIPT-Related String Theory Components in Z3

## Research Question

Examine the Z3 codebase and specifications in the `spec/` directory, focusing on code related to the ZIPT repository (https://github.com/CEisenhofer/ZIPT/tree/parikh/ZIPT) and the files for sgraph, seq_plugin, Nielsen graphs, theory_seq, and associated files for sequences (seq_rewriter, axioms for seq).

## Summary

This document provides a comprehensive analysis of Z3's string/sequence theory infrastructure and its relationship to the ZIPT reference implementation. Z3 has **two layers** of string solving:

1. **Existing production solver** (`theory_seq`): A mature, axiom-driven solver in `src/smt/` with 20+ final_check phases, regex derivatives, and Skolemization.
2. **New ZIPT-inspired infrastructure** (in progress): `sgraph` (string graph), `seq_plugin` (egraph plugin), and `nielsen_graph` (Nielsen transformations) — implementing the ZIPT approach of Nielsen-style word equation solving with lazy regex membership and Parikh image reasoning.

The spec directory (`spec/plan1.md`) describes the goal: implement `theory_nseq` as a new theory solver using the ZIPT algorithm, selectable via `smt.string_solver=nseq`. No `theory_nseq` files exist yet — only the foundational data structures (sgraph, snode, seq_plugin, nielsen_graph) are implemented and tested.

---

## Detailed Findings

### 1. ZIPT Reference Implementation (C#)

**Repository**: https://github.com/CEisenhofer/ZIPT (parikh branch)

The ZIPT solver implements Nielsen-style word equation solving with lazy regex membership and Parikh image analysis. It is a Z3 user-propagator written in C#.

#### Architecture

| Component | File(s) | Purpose |
|-----------|---------|---------|
| `StringPropagator` | `StringPropagator.cs` | Base user-propagator; handles Z3 callbacks (Fixed, Created, Eq, DisEq) |
| `NielsenGraph` | `Constraints/NielsenGraph.cs` | Search graph with iterative deepening DFS |
| `NielsenNode` | `Constraints/NielsenNode.cs` | Node = set of constraints; supports simplification and extension |
| `NielsenEdge` | `Constraints/NielsenEdge.cs` | Edge = substitutions + side constraints |
| `StrManager` | `Strings/StrManager.cs` | String canonicalization, concatenation, substitution |
| `PDD` | `IntUtils/PDD.cs` | Polynomial Decision Diagrams for integer reasoning |
| `Interval` | `IntUtils/Interval.cs` | Interval arithmetic for bounds |

#### Constraint Types

- **StrEq**: Word equations `LHS = RHS` (regex-free)
- **StrMem**: Regex membership `str ∈ L(regex)` with history tracking
- **IntEq**: Polynomial equality `P = 0` (over length variables)
- **IntLe**: Polynomial inequality `P ≤ 0`
- **IntNonEq**: Polynomial disequality `P ≠ 0`
- **Character ranges**: Symbolic char ∈ [a-z]
- **Character disequalities**: c₁ ≠ c₂

#### Modifier Chain (Priority Order)

1. **DetModifier** — Deterministic simplifications (highest priority)
2. **PowerEpsilonModifier** — Handle empty power: `u = "" || n = 0`
3. **NumCmpModifier** — Numeric comparisons: `n ≤ m || n > m`
4. **ConstNumUnwindingModifier** — Constant power unwinding: `n = 0 || n > 0`
5. **EqSplitModifier** — Split equality into prefix/suffix parts
6. **StarIntrModifier** — Introduce stabilizer `x ∈ base*`
7. **GPowerIntrModifier** — Introduce power `x := u^n prefix(u)`
8. **ConstNielsenModifier** — Nielsen split against constant: `x := ax || x := ""`
9. **RegexCharSplitModifier** — Character-level regex split via minterms
10. **RegexVarSplitModifier** — Variable-level regex split: `x / "" || x / cx`
11. **PowerSplitModifier** — Power unwinding
12. **VarNielsenModifier** — Variable Nielsen split (lowest priority)
13. **VarNumUnwindingModifier** — Variable power unwinding

#### Key Design Patterns

- **Lazy regex evaluation**: Only consume characters when concrete
- **Canonicalization**: All strings/polynomials are canonicalized
- **Parikh constraints**: Length reasoning via PDD polynomials + interval arithmetic
- **Iterative deepening**: Depth-bounded search with increasing limits
- **Subsumption**: Avoid redundant branches via node subsumption checking
- **Modification counts**: Version string variables for Z3 (x → x_0, x_1, ...)

---

### 2. sgraph — String Graph (`src/ast/euf/`)

**Files**: `euf_sgraph.h`, `euf_sgraph.cpp`, `euf_snode.h`

The sgraph maps Z3 AST expressions to `snode` (string node) structures organized as binary concatenation trees. This is the Z3-native equivalent of ZIPT's `StrManager`.

#### snode Class (`euf_snode.h`)

**snode_kind enum** (16 kinds):

| Kind | AST Op | Description |
|------|--------|-------------|
| `s_empty` | `OP_SEQ_EMPTY` | Empty string |
| `s_char` | `OP_SEQ_UNIT` (literal) | Concrete character |
| `s_var` | uninterpreted const | String variable |
| `s_unit` | `OP_SEQ_UNIT` (non-literal) | Generic unit |
| `s_concat` | `OP_SEQ_CONCAT` | Binary concatenation |
| `s_power` | `OP_SEQ_POWER` | String exponentiation s^n |
| `s_star` | `OP_RE_STAR` | Kleene star r* |
| `s_loop` | `OP_RE_LOOP` | Bounded loop r{lo,hi} |
| `s_union` | `OP_RE_UNION` | Union r₁\|r₂ |
| `s_intersect` | `OP_RE_INTERSECT` | Intersection r₁&r₂ |
| `s_complement` | `OP_RE_COMPLEMENT` | Complement ~r |
| `s_fail` | `OP_RE_EMPTY_SET` | Empty language ∅ |
| `s_full_char` | `OP_RE_FULL_CHAR_SET` | Full character set . |
| `s_full_seq` | `OP_RE_FULL_SEQ_SET` | Full sequence set .* |
| `s_to_re` | `OP_SEQ_TO_RE` | String to regex |
| `s_in_re` | `OP_SEQ_IN_RE` | Regex membership |
| `s_other` | (default) | Other expression |

**Key Members**:
- `expr* m_expr` — Z3 AST expression
- `snode_kind m_kind` — Classification
- `unsigned m_id` — Unique ID
- `bool m_ground` — No uninterpreted variables in subtree
- `bool m_regex_free` — No regex constructs in subtree
- `bool m_nullable` — Accepts empty string
- `unsigned m_level` — Tree depth
- `unsigned m_length` — Token count (leaf count)
- `unsigned m_hash_matrix[2][2]` — 2×2 polynomial hash matrix for O(1) associative hashing
- `snode_subst_cache* m_subst_cache` — ZIPT-style substitution cache
- `snode* m_args[0]` — Flexible array of children

**Hash Matrix** (`HASH_BASE = 31`):
- Empty: identity matrix `[[1,0],[0,1]]`
- Leaf: `[[31, expr_id+1], [0, 1]]`
- Concat: matrix multiplication `M(left) * M(right)`
- Hash value: `m_hash_matrix[0][1]` (assoc_hash)

**Navigation**: `first()`, `last()`, `at(i)`, `collect_tokens()`, `is_token()` (everything except empty and concat)

#### sgraph Class (`euf_sgraph.h/cpp`)

**Constructor**: `sgraph(ast_manager& m, egraph& eg, bool add_plugin = true)`
- Stores reference to egraph (not owned)
- If `add_plugin=true`, creates and registers `seq_plugin`
- Registers `on_make` callback with egraph: when any enode is created with seq/re sort, automatically creates corresponding snode

**Core Operations**:

| Method | Description |
|--------|-------------|
| `mk(expr* e)` | Create snode from expression (idempotent) |
| `find(expr* e)` | Lookup existing snode |
| `mk_var(symbol)` | Create variable snode |
| `mk_char(unsigned)` | Create character snode |
| `mk_empty()` | Create empty snode |
| `mk_concat(a, b)` | Create concat (with identity elimination) |
| `drop_first/last(n)` | Remove first/last token |
| `drop_left/right(n, k)` | Remove k tokens from left/right |
| `subst(n, var, repl)` | Substitute variable with replacement (cached) |
| `brzozowski_deriv(re, elem)` | Regex derivative via seq_rewriter |
| `compute_minterms(re, out)` | Extract character classes (capped at 20 predicates) |
| `push()/pop(n)` | Scope management synchronized with egraph |

**Substitution Caching**: Each snode has lazy-allocated `snode_subst_cache` storing `(var_id, repl_id) → result` mappings, avoiding redundant substitution computations (ZIPT pattern).

---

### 3. seq_plugin — Egraph Plugin (`src/ast/euf/`)

**Files**: `euf_seq_plugin.h`, `euf_seq_plugin.cpp`

The seq_plugin implements equality saturation for sequence/regex concatenation in the egraph. It handles associativity, identity/absorption rules, and Kleene star simplifications.

#### Class Hierarchy

```
euf::plugin (abstract base)
  └── euf::seq_plugin
```

**Constructor**: `seq_plugin(egraph& g, sgraph* sg = nullptr)`
- If `sg` is null, creates and owns a new sgraph
- Initializes `seq_util`, `seq_rewriter`, hash table with custom functors

#### Concat Handling

| Predicate | String | Regex |
|-----------|--------|-------|
| Concat | `is_str_concat()` / `OP_SEQ_CONCAT` | `is_re_concat()` / `OP_RE_CONCAT` |
| Identity | `is_str_empty()` / ε | `is_re_epsilon()` / to_re("") |
| Absorbing | (none) | `is_re_empty()` / ∅ |

**Simplification Rules** (from `propagate_simplify`):

1. **Kleene star merging**: `concat(v*, v*) = v*` when bodies are congruent (root equality)
2. **Extended star merging**: `concat(v*, concat(v*, c)) = concat(v*, c)`
3. **Nullable absorption**: `concat(.*, v) = .*` when v is nullable
4. **Symmetric nullable absorption**: `concat(v, .*) = .*` when v is nullable

**Associativity** (from `propagate_assoc`):
- Maintains `hashtable<enode*, enode_concat_hash, enode_concat_eq>` that respects associativity
- Hash: Uses sgraph's cached snode hash matrices for O(1) hashing, or falls back to leaf-based hashing
- Equality: Compares flattened leaf sequences pointwise
- When duplicate found, merges via `push_merge`

**Nullability**: Delegates to `m_rewriter.is_nullable(e)` (from `seq_rewriter`)

**Key Relationship**: seq_plugin does NOT create snodes. The sgraph's `on_make` callback handles snode creation. seq_plugin only observes egraph events and triggers merges.

---

### 4. Nielsen Graph (`src/smt/seq/`)

**Files**: `seq_nielsen.h`, `seq_nielsen.cpp`, `CMakeLists.txt`

The Nielsen graph implements word equation solving via Nielsen transformations. This is the Z3-native port of ZIPT's `NielsenGraph`, `NielsenNode`, `NielsenEdge`, and constraint types.

#### Classes

##### dep_tracker (`seq_nielsen.h:81-94`)
Bitvector-based dependency tracker for conflict explanation.
- `merge(other)`: Bitwise OR
- `is_superset(other)`: All bits of other present
- `is_empty()`: No bits set

##### str_eq (`seq_nielsen.h:98-119`)
Word equation `lhs = rhs` (both regex-free snode trees).
- `sort()`: Canonicalize by snode ID
- `is_trivial()`: Same snode or both empty
- `contains_var(var)`: Check if variable appears in lhs or rhs

##### str_mem (`seq_nielsen.h:123-143`)
Regex membership `str ∈ L(regex)`.
- `m_history`: Consumed prefix for cycle detection
- `m_id`: Unique identifier
- `is_primitive()`: True when str is a single variable

##### nielsen_subst (`seq_nielsen.h:147-162`)
Variable substitution `var → replacement`.
- `is_eliminating()`: True when variable doesn't appear in replacement (progress)

##### nielsen_edge (`seq_nielsen.h:166-195`)
Directed edge in the Nielsen graph.
- `m_subst`: Vector of substitutions applied
- `m_side_str_eq/m_side_str_mem`: Side constraints added
- `m_is_progress`: Whether this is an eliminating step

##### nielsen_node (`seq_nielsen.h:199-270`)
Node = set of constraints at a point in the search.
- `m_str_eq`: String equality constraints
- `m_str_mem`: Regex membership constraints
- `m_outgoing`: Outgoing edges
- `m_backedge`: For cycle detection
- `m_is_general_conflict`, `m_reason`: Conflict tracking
- `clone_from(parent)`: Copy constraints
- `apply_subst(sg, s)`: Apply substitution to all constraints

##### nielsen_graph (`seq_nielsen.h:274-325`)
The overall graph structure.
- `m_sg`: Reference to sgraph infrastructure
- `m_root`: Root node with initial constraints
- `m_run_idx`, `m_depth_bound`: For iterative deepening
- `mk_node()`, `mk_child(parent)`, `mk_edge(src, tgt, progress)`
- `add_str_eq(lhs, rhs)`, `add_str_mem(str, regex)`: Populate from external solver
- `reset()`, `inc_run_idx()`: Lifecycle management

#### Enums

**simplify_result**: `proceed`, `conflict`, `satisfied`, `restart`, `restart_and_satisfied`

**backtrack_reason**: `unevaluated`, `extended`, `symbol_clash`, `parikh_image`, `subsumption`, `arithmetic`, `regex`, `regex_widening`, `character_range`, `smt`, `children_failed`

#### Build Configuration

`src/smt/seq/CMakeLists.txt`: Component `smt_seq`, depends on `euf` and `rewriter`.

#### Current Status

The Nielsen graph provides **data structures and infrastructure** — node/edge/constraint/substitution management, dependency tracking, backtracking support, display. The **actual transformation algorithms** (modifier chain, graph expansion, conflict detection, Parikh image analysis) are not yet implemented. Tests cover all data structure operations but not algorithmic behavior.

---

### 5. theory_seq — Existing String Theory Solver (`src/smt/`)

**Files**: `theory_seq.h`, `theory_seq.cpp`, `theory_seq_empty.h`

The production string solver implementing `theory` interface. Uses axiom-driven solving with 20+ cascading phases.

#### Class Structure

```
smt::theory (base)
seq::eq_solver_context (interface)
  └── smt::theory_seq
```

**Component Submodules** (declared in `theory_seq.h:356-366`):
- `seq::skolem m_sk` — Skolemization
- `seq_axioms m_ax` — Axiom generation (bridges rewriter and SMT layers)
- `seq::eq_solver m_eq` — Core equality solver (solver-agnostic)
- `seq_regex m_regex` — Regular expression handling
- `seq_offset_eq m_offset_eq` — Length offset tracking
- `th_union_find m_find` — Union-find for theory variables
- `dependency_manager m_dm` — Justification tracking
- `solution_map m_rep` — Variable → representative mapping

#### Final Check Cascade (20 phases)

```
1.  simplify_and_solve_eqs()     — Solve unitary equalities
2.  check_lts()                   — Lexicographic ordering
3.  solve_nqs(0)                  — Disequalities
4.  m_regex.propagate()           — Regex propagation
5.  check_contains()              — Contains constraints
6.  check_fixed_length(true,false)— Zero-length sequences
7.  len_based_split()             — Length-based splitting
8.  check_fixed_length(false,false)— Fixed-length expansion
9.  check_int_string()            — int/string conversions
10. check_ubv_string()            — bitvector/string conversions
11. reduce_length_eq()            — Reduce by length equality
12. branch_unit_variable()        — Branch on unit variables
13. branch_binary_variable()      — Branch on binary patterns
14. branch_variable()             — General variable branching
15. check_length_coherence()      — Length coherence
16. check_extensionality()        — Extensionality
17. branch_nqs()                  — Branch on disequalities
18. branch_itos()                 — Branch on int-to-string
19. check_fixed_length(false,true)— Fixed-length (long strings)
20. solve_recfuns()               — Recursive functions
```

Returns `FC_CONTINUE` if progress, `FC_GIVEUP` if stuck, `FC_DONE` if solved.

#### String Solver Selection (`smt_setup.cpp`)

Parameter: `smt.string_solver`
- `"seq"` → `setup_seq()` → `alloc(smt::theory_seq, m_context)`
- `"empty"` → `setup_seq()` (with empty variant)
- `"none"` → No solver
- `"auto"` → `setup_seq()`
- `"nseq"` → **Not yet implemented** (planned per spec)

#### Key Data Structures

- `solution_map m_rep` — Maps variables to representatives (with normalization cache)
- `scoped_vector<depeq> m_eqs` — Active equations
- `scoped_vector<ne> m_nqs` — Disequalities
- `scoped_vector<nc> m_ncs` — Negated contains
- `exclusion_table m_exclude` — Asserted disequalities
- `expr_ref_vector m_axioms` — Axiom queue (with deduplication)

---

### 6. seq_rewriter — Sequence Rewriter (`src/ast/rewriter/`)

**Files**: `seq_rewriter.h`, `seq_rewriter.cpp`

Provides local syntactic simplification rules for all string/sequence operations. Entry point: `mk_app_core(func_decl* f, ...)`.

#### Rewrite Categories

| Category | Key Methods | Description |
|----------|-------------|-------------|
| Construction | `mk_seq_unit`, `mk_seq_concat` | Coalesce chars, right-associate, eliminate empty |
| Extraction | `mk_seq_extract`, `mk_seq_at`, `mk_seq_nth` | Substring, index access |
| Length | `mk_seq_length` | Compute length, simplify for concat/replace/extract |
| Search | `mk_seq_contains`, `mk_seq_index`, `mk_seq_last_index` | Containment, index-of |
| Replacement | `mk_seq_replace`, `mk_seq_replace_all`, `mk_seq_replace_re*` | String replacement |
| Comparison | `mk_str_le`, `mk_str_lt`, `mk_seq_prefix`, `mk_seq_suffix` | Lexicographic, prefix/suffix |
| Conversion | `mk_str_itos`, `mk_str_stoi`, `mk_str_from_code`, `mk_str_to_code` | Type conversions |
| Higher-order | `mk_seq_map`, `mk_seq_mapi`, `mk_seq_foldl`, `mk_seq_foldli` | Map, fold |
| Regex | `mk_re_concat`, `mk_re_union`, `mk_re_inter`, `mk_re_star`, etc. | Regex construction |
| Derivative | `mk_re_derivative` → `mk_antimirov_deriv` | Antimirov-style regex derivative |
| Nullability | `is_nullable` → `is_nullable_rec` | Nullable check for regex |

#### Regex Derivative System

Uses **Antimirov derivatives** with a BDD-like normal form:

1. **Top level**: Union of Antimirov derivatives using `_OP_RE_ANTIMIROV_UNION`
2. **Middle level**: Nested if-then-else sorted by condition ID
3. **Leaf level**: Regular regex unions

Key derivative rules:
- `D(e, r₁·r₂) = D(e,r₁)·r₂ ∪ (nullable(r₁) ? D(e,r₂) : ∅)`
- `D(e, r₁∪r₂) = D(e,r₁) ∪ D(e,r₂)`
- `D(e, r*) = D(e,r)·r*`
- `D(e, ¬r) = ¬D(e,r)`
- `D(e, [lo-hi]) = ε if lo ≤ e ≤ hi else ∅`

Validated by `check_deriv_normal_form` in debug mode.

---

### 7. Axiom System (`src/ast/rewriter/` + `src/smt/`)

Two layers: **rewriter-level** (solver-independent) and **SMT-level** (bridges to Z3 context).

#### Rewriter-Level Axioms (`seq::axioms`, `src/ast/rewriter/seq_axioms.h/cpp`)

Solver-agnostic axiom generation via callbacks. Key axioms:

| Operation | Axiom Summary |
|-----------|---------------|
| `extract(s,i,l)` | `0≤i≤\|s\| ∧ 0≤l → s=x·e·y ∧ \|x\|=i ∧ \|e\|=min(l,\|s\|-i)` |
| `indexof(t,s,off)` | `contains(t,s) → t=x·s·y ∧ indexof=\|x\|` + tightest prefix |
| `replace(u,s,t)` | `contains(u,s) → u=x·s·y ∧ r=x·t·y` |
| `at(s,i)` | `0≤i<\|s\| → s=x·e·y ∧ \|x\|=i ∧ \|e\|=1` |
| `itos(n)` | `n≥0 → stoi(itos(n))=n ∧ no leading zeros` |
| `stoi(s)` | `stoi(s)≥-1 ∧ stoi("")=-1` |

Introduced via Skolem functions (see below).

#### SMT-Level Axioms (`smt::seq_axioms`, `src/smt/seq_axioms.h/cpp`)

Wraps `seq::axioms` with literal creation, clause addition, and phase forcing for Z3's SMT context.

---

### 8. Skolemization (`src/ast/rewriter/seq_skolem.h/cpp`)

`seq::skolem` introduces auxiliary Skolem functions for structural reasoning:

| Skolem | Symbol | Purpose |
|--------|--------|---------|
| `seq.pre` | `m_pre` | Prefix of s up to index i |
| `seq.post` | `m_post` | Suffix of s from index i |
| `seq.tail` | `m_tail` | Rest after first element |
| `seq.first` | `m_seq_first` | First element |
| `seq.last` | `m_seq_last` | Last element |
| `seq.idx.l/r` | `m_indexof_left/right` | Decomposition for indexof: t = left·s·right |
| `seq.lidx.l/r` | `m_lindexof_left/right` | Decomposition for last_indexof |
| `seq.cnt.l/r` | — | Decomposition for contains |
| `aut.accept` | `m_accept` | Regex automaton acceptance |
| `aut.step` | `m_aut_step` | Automaton state transition |
| `seq.eq` | `m_eq` | Special equality predicate |
| `seq.length_limit` | `m_length_limit` | Length bound |

---

### 9. seq_decl_plugin — Declaration Plugin (`src/ast/`)

**Files**: `seq_decl_plugin.h`, `seq_decl_plugin.cpp`

Provides the theory declarations for sequences, strings, and regular expressions.

#### Operation Kinds (`seq_op_kind` enum)

**Sequence**: `OP_SEQ_UNIT`, `OP_SEQ_EMPTY`, `OP_SEQ_CONCAT`, `OP_SEQ_PREFIX`, `OP_SEQ_SUFFIX`, `OP_SEQ_CONTAINS`, `OP_SEQ_EXTRACT`, `OP_SEQ_REPLACE`, `OP_SEQ_AT`, `OP_SEQ_NTH`, `OP_SEQ_NTH_I`, `OP_SEQ_NTH_U`, `OP_SEQ_LENGTH`, `OP_SEQ_INDEX`, `OP_SEQ_LAST_INDEX`, `OP_SEQ_TO_RE`, `OP_SEQ_IN_RE`, `OP_SEQ_REPLACE_RE_ALL`, `OP_SEQ_REPLACE_RE`, `OP_SEQ_REPLACE_ALL`, `OP_SEQ_MAP`, `OP_SEQ_MAPI`, `OP_SEQ_FOLDL`, `OP_SEQ_FOLDLI`, **`OP_SEQ_POWER`**

**Regex**: `OP_RE_PLUS`, `OP_RE_STAR`, `OP_RE_OPTION`, `OP_RE_RANGE`, `OP_RE_CONCAT`, `OP_RE_UNION`, `OP_RE_DIFF`, `OP_RE_INTERSECT`, `OP_RE_LOOP`, `OP_RE_POWER`, `OP_RE_COMPLEMENT`, `OP_RE_EMPTY_SET`, `OP_RE_FULL_SEQ_SET`, `OP_RE_FULL_CHAR_SET`, `OP_RE_OF_PRED`, `OP_RE_REVERSE`, `OP_RE_DERIVATIVE`

**String-specific**: `OP_STRING_CONST`, `OP_STRING_ITOS`, `OP_STRING_STOI`, `OP_STRING_UBVTOS`, `OP_STRING_SBVTOS`, `OP_STRING_LT`, `OP_STRING_LE`, `OP_STRING_IS_DIGIT`, `OP_STRING_TO_CODE`, `OP_STRING_FROM_CODE`

#### seq_util Utility Class

Nested classes for operation construction/recognition:
- `seq_util::str` — String/sequence operations (`mk_concat`, `mk_length`, `mk_empty`, `is_concat`, `is_empty`, `mk_power`, `is_power`, etc.)
- `seq_util::rex` — Regex operations (`mk_star`, `mk_union`, `mk_inter`, `mk_complement`, `mk_concat`, `is_star`, `is_concat`, `is_nullable`, etc.)

#### Sort System

- `SEQ_SORT` — Generic Seq[T]
- `RE_SORT` — RegEx[Seq[T]]
- `_STRING_SORT` — Seq[Char] (string)
- `_REGLAN_SORT` — RegEx[String]

---

### 10. Sequence Equality Solver (`src/ast/rewriter/seq_eq_solver.h/cpp`)

Solver-agnostic equality inference for sequence equations:

- `reduce_unit`: Handle unit equations
- `reduce_itos1/2/3`: Handle `itos(s) = itos(t)`, `itos(s) = ""`, `itos(n) = "d1d2...dk"`
- `reduce_binary_eq`: Handle `x·xs = ys·y` patterns
- `reduce_nth_solved`: Solve nth equations
- `branch_unit_variable`: Split variable as empty or non-empty

---

### 11. Test Infrastructure

#### Test Files

| File | Tests | Lines | Component |
|------|-------|-------|-----------|
| `src/test/euf_sgraph.cpp` | 18 | 769 | sgraph: classification, metadata, backtracking, navigation, substitution, derivatives, minterms |
| `src/test/euf_seq_plugin.cpp` | 7 | 242 | seq_plugin: associativity, identity elimination, star merging, nullable absorption, egraph sync |
| `src/test/seq_nielsen.cpp` | 13 | 480 | Nielsen: dep_tracker, str_eq, str_mem, subst, node, edge, graph population, expansion, backedge |

#### Registration

- `src/test/main.cpp`: `TST(euf_sgraph)` (line 284), `TST(euf_seq_plugin)` (line 285), `TST(seq_nielsen)` (line 289)
- `src/test/CMakeLists.txt`: All three .cpp files included; depends on `smt_seq`
- Build: `ninja test-z3`, Run: `./test-z3 euf_sgraph`, `./test-z3 euf_seq_plugin`, `./test-z3 seq_nielsen`

#### Test Setup Pattern

```cpp
ast_manager m;
reg_decl_plugins(m);
euf::egraph eg(m);
euf::sgraph sg(m, eg);        // Creates seq_plugin automatically
seq_util seq(m);
sort_ref str_sort(seq.str.mk_string_sort(), m);
// For nielsen:
seq::nielsen_graph ng(sg);
```

---

## Code References

### ZIPT Infrastructure (New)

| File | Description |
|------|-------------|
| `src/ast/euf/euf_snode.h` | snode class, snode_kind enum, hash matrix, subst cache |
| `src/ast/euf/euf_sgraph.h` | sgraph class header |
| `src/ast/euf/euf_sgraph.cpp` | sgraph implementation (classify, metadata, hash, subst, derivatives, minterms) |
| `src/ast/euf/euf_seq_plugin.h` | seq_plugin class header |
| `src/ast/euf/euf_seq_plugin.cpp` | seq_plugin implementation (assoc, simplify, nullable) |
| `src/smt/seq/seq_nielsen.h` | Nielsen graph classes (str_eq, str_mem, subst, edge, node, graph) |
| `src/smt/seq/seq_nielsen.cpp` | Nielsen graph implementation |
| `src/smt/seq/CMakeLists.txt` | smt_seq component build config |

### Existing String Theory (Production)

| File | Description |
|------|-------------|
| `src/smt/theory_seq.h` | theory_seq class with 20-phase final_check |
| `src/smt/theory_seq.cpp` | Full theory solver implementation |
| `src/smt/theory_seq_empty.h` | Empty/stub variant |
| `src/smt/seq_axioms.h/cpp` | SMT-level axiom bridge |
| `src/smt/seq_regex.h/cpp` | Regex handling for theory_seq |
| `src/smt/seq_eq_solver.cpp` | SMT-level equality solving |
| `src/smt/seq_ne_solver.cpp` | Disequality solving |
| `src/smt/seq_offset_eq.h/cpp` | Length offset equality |
| `src/smt/smt_setup.h/cpp` | String solver selection/instantiation |

### Rewriter Layer (Shared)

| File | Description |
|------|-------------|
| `src/ast/rewriter/seq_rewriter.h/cpp` | Rewrite rules + regex derivatives |
| `src/ast/rewriter/seq_axioms.h/cpp` | Solver-independent axiom generation |
| `src/ast/rewriter/seq_skolem.h/cpp` | Skolem function introduction |
| `src/ast/rewriter/seq_eq_solver.h/cpp` | Solver-agnostic equality inference |

### Declaration Layer

| File | Description |
|------|-------------|
| `src/ast/seq_decl_plugin.h/cpp` | Sort/operation declarations, seq_util |
| `src/model/seq_factory.h` | Model value factory |
| `src/params/theory_seq_params.h/cpp` | Theory parameters |
| `src/params/seq_rewriter_params.pyg` | Rewriter parameters |

### Tests

| File | Description |
|------|-------------|
| `src/test/euf_sgraph.cpp` | 18 sgraph unit tests |
| `src/test/euf_seq_plugin.cpp` | 7 seq_plugin tests |
| `src/test/seq_nielsen.cpp` | 13 Nielsen graph tests |
| `src/test/main.cpp` | Test registration (lines 284, 285, 289) |
| `src/test/CMakeLists.txt` | Test build config (lines 54, 55, 134) |

---

## Architecture Documentation

### Component Dependency Graph

```
seq_decl_plugin  (AST sort/op declarations)
    ↓
seq_util  (utility wrapper)
    ↓
seq_rewriter  (simplification rules, derivatives)
    ↓ ↘
seq_axioms (rewriter)    seq_skolem
    ↓                       ↓
seq_axioms (SMT)   ←───────┘
    ↓
┌────────────┬──────────────────────┐
│ theory_seq │  theory_nseq (TODO)  │
│ (existing) │  (per spec/plan1.md) │
├────────────┤──────────────────────┤
│ seq_regex  │  nielsen_graph ←──── sgraph ←── snode
│ seq_eq/ne  │  (new ZIPT infra)    seq_plugin
│ solution_map│                      egraph
└────────────┴──────────────────────┘
```

### ZIPT ↔ Z3 Component Mapping

| ZIPT (C#) | Z3 (C++) | Location |
|------------|----------|----------|
| `StrManager` | `sgraph` + `snode` | `src/ast/euf/euf_sgraph.*`, `euf_snode.h` |
| `Str` (token tree) | `snode` (binary concat tree) | `src/ast/euf/euf_snode.h` |
| `StrEq` | `seq::str_eq` | `src/smt/seq/seq_nielsen.h:98` |
| `StrMem` | `seq::str_mem` | `src/smt/seq/seq_nielsen.h:123` |
| `NielsenGraph` | `seq::nielsen_graph` | `src/smt/seq/seq_nielsen.h:274` |
| `NielsenNode` | `seq::nielsen_node` | `src/smt/seq/seq_nielsen.h:199` |
| `NielsenEdge` | `seq::nielsen_edge` | `src/smt/seq/seq_nielsen.h:166` |
| `Subst` | `seq::nielsen_subst` | `src/smt/seq/seq_nielsen.h:147` |
| `DependencyTracker` | `seq::dep_tracker` | `src/smt/seq/seq_nielsen.h:81` |
| `SimplifyResult` | `seq::simplify_result` | `src/smt/seq/seq_nielsen.h:54` |
| `BacktrackReasons` | `seq::backtrack_reason` | `src/smt/seq/seq_nielsen.h:64` |
| `PDD` / `Interval` | (not yet ported) | — |
| Modifier chain | (not yet ported) | — |
| `StringPropagator` | `theory_nseq` (TODO) | — |

### What Exists vs. What's Planned

**Implemented**:
- ✅ sgraph + snode (string representation, metadata, hashing, substitution, derivatives, minterms)
- ✅ seq_plugin (associativity, identity, absorption, star merge, nullable absorption)
- ✅ Nielsen graph data structures (str_eq, str_mem, subst, edge, node, graph, dep_tracker)
- ✅ All unit tests passing (18 + 7 + 13 = 38 tests)

**Not Yet Implemented** (per spec/plan1.md):
- ❌ `theory_nseq` skeleton and SMT integration
- ❌ Parameter integration (`smt.string_solver=nseq`)
- ❌ Nielsen transformation algorithms (modifier chain)
- ❌ Graph expansion / iterative deepening search
- ❌ Conflict detection and explanation
- ❌ Parikh image / PDD / Interval reasoning
- ❌ Regex splitting modifiers
- ❌ String propagator (propagation engine)
- ❌ Model generation
- ❌ Integration tests

---

## Historical Context (from spec/)

### spec/reference.md
Points to ZIPT repository (parikh branch) and two PDF papers:
- `LazyMemberships.pdf` — Lazy regex membership approach
- `ClemensTableau.pdf` — Additional tableau algorithms

### spec/plan.md
Task description: Implement `theory_nseq` in `src/smt/`, add `smt.string_solver` parameter support, put self-contained utilities in `ast/rewriter/`.

### spec/plan1.md
Detailed implementation plan with 7 phases:
1. Skeleton & Integration
2. Core Data Structures (state, constraints, dependencies)
3. Word Equation Solver (Nielsen transformations)
4. Length Constraint Integration (Parikh image)
5. Regex Membership
6. Propagation Engine
7. Model Generation

---

## Open Questions

1. **theory_nseq skeleton**: When will Phase 1 (skeleton + parameter integration) be implemented?
2. **Modifier chain priority**: Should Z3's modifier priorities match ZIPT's exactly, or be adjusted?
3. **PDD porting**: Will Z3 reuse existing polynomial infrastructure or port ZIPT's PDD?
4. **Regex derivatives**: Will `theory_nseq` reuse `seq_rewriter::mk_derivative` or implement ZIPT's approach?
5. **Integer solver integration**: Will `theory_nseq` use `arith_value` (like `theory_seq`) or a sub-solver (like ZIPT)?
6. **Backtracking scope**: How will Nielsen graph state interact with SMT solver backtracking?
7. **Performance target**: What benchmarks should `theory_nseq` match or exceed compared to `theory_seq`?
