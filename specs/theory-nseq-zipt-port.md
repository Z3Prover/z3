# theory_nseq — ZIPT-Based String Theory Solver for Z3

| Document Metadata      | Details                            |
| ---------------------- | ---------------------------------- |
| Author(s)              | Nikolaj Bjorner                    |
| Status                 | In Review (RFC)                    |
| Team / Owner           | Z3 / SMT Strings                   |
| Created / Last Updated | 2026-03-03                         |

## 1. Executive Summary

This spec defines the completion of the ZIPT algorithm port into Z3's c3 branch as `theory_nseq` — a new string/sequence theory solver based on Nielsen-style word equation solving with lazy regex membership and Parikh image reasoning. The foundational data structures (sgraph, snode, seq_plugin, nielsen_graph) are already implemented and tested (38 unit tests). What remains is: (1) the theory solver skeleton and SMT integration, (2) the Nielsen transformation algorithms (modifier chain, graph expansion, iterative deepening, conflict detection), (3) Parikh image / length reasoning, (4) regex membership processing, (5) propagation engine, and (6) model generation. The new solver will coexist with `theory_seq` and be selectable via `smt.string_solver=nseq`.

## 2. Context and Motivation

### 2.1 Current State

Z3's string solver `theory_seq` uses an axiom-driven approach with a 20-phase `final_check_eh` cascade. While production-grade, it struggles with certain classes of word equations and regex membership constraints that the ZIPT algorithm handles more effectively.

The ZIPT algorithm (reference C# implementation at [github.com/CEisenhofer/ZIPT](https://github.com/CEisenhofer/ZIPT/tree/parikh/ZIPT)) uses a fundamentally different approach: Nielsen transformations on a search graph with iterative deepening, lazy regex evaluation, and Parikh image constraints.

**Already implemented on c3 branch** (per [research doc](../../research/docs/2026-03-03-zipt-string-theory-codebase-analysis.md)):
- ✅ `sgraph` + `snode` — String representation, metadata, hashing, substitution, derivatives, minterms (`src/ast/euf/euf_sgraph.h/.cpp`, `euf_snode.h`)
- ✅ `seq_plugin` — Egraph plugin for associativity, identity, absorption, star merge (`src/ast/euf/euf_seq_plugin.h/.cpp`)
- ✅ Nielsen graph data structures — `str_eq`, `str_mem`, `nielsen_subst`, `nielsen_edge`, `nielsen_node`, `nielsen_graph`, `dep_tracker` (`src/smt/seq/seq_nielsen.h/.cpp`)
- ✅ 38 unit tests (18 sgraph + 7 seq_plugin + 13 nielsen)

**Not yet implemented:**
- ❌ `theory_nseq` skeleton and SMT integration
- ❌ Parameter integration (`smt.string_solver=nseq`)
- ❌ Nielsen transformation algorithms (modifier chain, 13 modifiers)
- ❌ Graph expansion / iterative deepening DFS
- ❌ Constraint simplification engine
- ❌ Conflict detection and explanation
- ❌ Subsumption checking
- ❌ Parikh image / PDD / Interval reasoning
- ❌ Regex splitting modifiers
- ❌ Propagation engine
- ❌ Model generation

### 2.2 The Problem

- **Algorithmic gap**: The core solving algorithms — the "brain" of ZIPT — have not been ported. Only the "bones" (data structures) exist.
- **No solver entry point**: There is no `theory_nseq` class, so the ZIPT algorithm cannot be invoked from Z3.
- **Missing search**: Iterative deepening, subsumption, and conflict detection are absent.
- **Missing reasoning**: Parikh image (length constraints via polynomial decision diagrams) and regex splitting modifiers are absent.

### 2.3 Reference Documents

- `spec/reference.md` — Points to ZIPT repo (parikh branch), LazyMemberships.pdf, ClemensTableau.pdf
- `spec/plan.md` — Task description
- `spec/plan1.md` — 7-phase implementation plan with file list
- `research/docs/2026-03-03-zipt-string-theory-codebase-analysis.md` — Comprehensive codebase research

## 3. Goals and Non-Goals

### 3.1 Functional Goals

- [ ] `theory_nseq` theory solver class implementing `smt::theory` interface
- [ ] Selectable via `smt.string_solver=nseq` parameter
- [ ] Nielsen transformation-based word equation solving
- [ ] Lazy regex membership via Brzozowski derivatives (reusing `sgraph::brzozowski_deriv`)
- [ ] Parikh image / length constraint reasoning
- [ ] Iterative deepening search with depth bounds
- [ ] Subsumption-based pruning
- [ ] Conflict detection with dependency-tracked explanations
- [ ] Model generation for satisfiable instances
- [ ] Correct results on Z3's existing string regression suite (`C:\z3test\regressions\smt2\string*.smt2`)

### 3.2 Non-Goals (Out of Scope)

- [ ] Replacing `theory_seq` as default — `theory_nseq` is an alternative, not a replacement
- [ ] Polymorphic sequences — focus on strings (`Seq[Char]`) initially; generic `Seq[T]` can follow later
- [ ] Higher-order sequence ops (`seq.map`, `seq.foldl`) — defer to `theory_seq` or axiomatize minimally
- [ ] Bitvector-to-string conversions (`ubv2s`, `sbv2s`) — defer
- [ ] New Z3 API surface — `theory_nseq` is internal only, selected by parameter
- [ ] Performance parity with `theory_seq` on all benchmarks in Phase 1 — correctness first

## 4. Proposed Solution (High-Level Design)

### 4.1 System Architecture

```
┌─────────────────────────────────────────────────────────┐
│                    smt::context                          │
│  ┌──────────────┐  ┌──────────────┐  ┌──────────────┐  │
│  │ theory_arith │  │ theory_nseq  │  │ theory_bv    │  │
│  └──────────────┘  └──────┬───────┘  └──────────────┘  │
│                           │                              │
│  ┌────────────────────────┼──────────────────────────┐  │
│  │            theory_nseq internals                   │  │
│  │  ┌─────────────┐  ┌───┴───────┐  ┌────────────┐  │  │
│  │  │ nseq_regex  │  │ propagator│  │ nseq_model │  │  │
│  │  └──────┬──────┘  └───┬───────┘  └────────────┘  │  │
│  │         │             │                            │  │
│  │  ┌──────┴─────────────┴────────────────────────┐  │  │
│  │  │          nielsen_graph (search engine)       │  │  │
│  │  │  ┌──────────┐ ┌──────────┐ ┌─────────────┐ │  │  │
│  │  │  │ modifier │ │ simplify │ │ subsumption │ │  │  │
│  │  │  │  chain   │ │  engine  │ │   checker   │ │  │  │
│  │  │  └──────────┘ └──────────┘ └─────────────┘ │  │  │
│  │  └───────────────────┬─────────────────────────┘  │  │
│  │                      │                             │  │
│  │  ┌───────────────────┴─────────────────────────┐  │  │
│  │  │              sgraph + snode                  │  │  │
│  │  │       (string representation layer)          │  │  │
│  │  └─────────────────────────────────────────────┘  │  │
│  └────────────────────────────────────────────────────┘  │
│                                                          │
│  Shared infrastructure: seq_util, seq_rewriter,          │
│  seq_skolem, arith_value, seq_factory                    │
└──────────────────────────────────────────────────────────┘
```

### 4.2 Architectural Pattern

**Nielsen transformation graph with iterative deepening DFS** — matching ZIPT's architecture:

1. **Internalization**: String terms/atoms are registered, creating theory variables and snode representations.
2. **Propagation**: Equality/disequality merges and boolean assignments update the constraint store.
3. **Final check**: Build a nielsen_graph from active constraints, run iterative deepening search.
4. **Search**: At each node, apply the modifier chain (13 modifiers in priority order) to generate child nodes. Check for conflicts, subsumption, and satisfaction.
5. **Conflict/Satisfaction**: If all leaves are satisfied → FC_DONE. If a conflict is found → generate explanation clause and return FC_CONTINUE. If stuck → increase depth bound and retry.

### 4.3 Key Components

| Component | Responsibility | Location | Reuse |
|-----------|---------------|----------|-------|
| `theory_nseq` | SMT theory interface, internalization, propagation | `src/smt/theory_nseq.h/.cpp` | New |
| `nseq_state` | Constraint store, variable tracking, backtrackable state | `src/smt/nseq_state.h/.cpp` | New |
| Nielsen graph (solver) | Graph expansion, iterative deepening, conflict detection | `src/smt/seq/seq_nielsen.h/.cpp` | Extend existing |
| Nielsen modifiers | 13 transformation rules (per ZIPT modifier chain) | `src/smt/seq/seq_nielsen.h/.cpp` | New (in existing files) |
| `nseq_regex` | Regex membership processing, derivative dispatch | `src/smt/nseq_regex.h/.cpp` | New |
| `nseq_model` | Model construction from solved constraints | `src/smt/nseq_model.h/.cpp` | New |
| Parikh/length | Length reasoning, polynomial constraints | `src/smt/seq/seq_nielsen.h/.cpp` | New (in existing) |
| sgraph | String representation, substitution, derivatives | `src/ast/euf/euf_sgraph.*` | Existing ✅ |
| seq_plugin | Egraph associativity/simplification | `src/ast/euf/euf_seq_plugin.*` | Existing ✅ |
| seq_util | Sort/op declarations and utilities | `src/ast/seq_decl_plugin.*` | Existing ✅ |
| seq_rewriter | Rewrite rules, regex derivatives, nullability | `src/ast/rewriter/seq_rewriter.*` | Existing ✅ |
| seq_skolem | Skolem function introduction | `src/ast/rewriter/seq_skolem.*` | Existing ✅ |
| arith_value | Arithmetic solver queries | `src/smt/smt_arith_value.*` | Existing ✅ |
| seq_factory | Model value factory | `src/model/seq_factory.h` | Existing ✅ |

## 5. Detailed Design

### 5.1 Phase 1: Skeleton & Integration

#### 5.1.1 theory_nseq class (`src/smt/theory_nseq.h/.cpp`)

Implements `smt::theory` with these pure virtual methods:

```cpp
class theory_nseq : public theory {
    // Required by smt::theory:
    bool internalize_atom(app* atom, bool gate_ctx) override;
    bool internalize_term(app* term) override;
    void new_eq_eh(theory_var v1, theory_var v2) override;
    void new_diseq_eh(theory_var v1, theory_var v2) override;
    theory* mk_fresh(context* new_ctx) override;
    void display(std::ostream& out) const override;

    // Optional overrides:
    void assign_eh(bool_var v, bool is_true) override;
    bool can_propagate() override;
    void propagate() override;
    final_check_status final_check_eh() override;
    void push_scope_eh() override;
    void pop_scope_eh(unsigned num_scopes) override;
    void init_model(model_generator& mg) override;
    void finalize_model(model_generator& mg) override;
    void collect_statistics(statistics& st) const override;

    // Members:
    seq_util          m_seq;
    arith_util        m_autil;
    arith_value       m_arith_value;
    seq_rewriter      m_rewriter;
    seq::skolem       m_sk;
    euf::egraph       m_egraph;
    euf::sgraph       m_sgraph;
    nielsen_graph     m_nielsen;
    // ... state management, constraint store
};
```

**family_id**: Uses `m_seq.get_family_id()` (same as `theory_seq`).

**Internalization pattern** (following `theory_seq`):
- `internalize_term`: For string-sorted terms, create theory variable, register with egraph/sgraph. For `str.++`, `str.len`, `str.in_re`, etc., recursively internalize children.
- `internalize_atom`: For `str.in_re`, `str.contains`, `str.prefixof`, `str.suffixof`, `str.<`, `str.<=` — create boolean variable.

#### 5.1.2 Parameter integration

**`src/params/smt_params.cpp`** — Add `"nseq"` to `validate_string_solver()`:
```cpp
void smt_params::validate_string_solver(symbol const& s) const {
    if (s == "z3str3" || s == "seq" || s == "empty" || s == "auto" || s == "none" || s == "nseq")
        return;
    throw default_exception("Invalid string solver value. Legal values are z3str3, seq, empty, auto, none, nseq");
}
```

**`src/smt/smt_setup.cpp`** — Add `"nseq"` dispatch:
```cpp
void setup::setup_seq_str(static_features const& st) {
    if (m_params.m_string_solver == "nseq") {
        setup_nseq();
    }
    else if (m_params.m_string_solver == "seq") { ... }
    // ...
}

void setup::setup_nseq() {
    m_context.register_plugin(alloc(smt::theory_nseq, m_context));
}
```

**`src/smt/smt_setup.h`** — Declare `setup_nseq()`.

**`src/params/smt_params_helper.pyg`** — Document `nseq` in the `string_solver` parameter description.

#### 5.1.3 Build system

**`src/smt/CMakeLists.txt`** — Add `theory_nseq.cpp` and new .cpp files.

### 5.2 Phase 2: Constraint Store & State Management

#### 5.2.1 nseq_state (`src/smt/nseq_state.h/.cpp`)

Manages the backtrackable constraint store bridging SMT context to Nielsen graph:

```cpp
class nseq_state {
    // Variable tracking
    th_union_find           m_find;        // Union-find for theory variables
    obj_map<expr, theory_var> m_var_map;   // expr → theory_var

    // Active constraints (backtrackable)
    scoped_vector<str_eq>   m_eqs;         // Active word equations
    scoped_vector<str_mem>  m_mems;        // Active regex memberships
    svector<std::pair<theory_var, theory_var>> m_diseqs; // Disequalities
    svector<bool_var>       m_pending_bools; // Pending boolean assignments

    // Scope management
    void push();
    void pop(unsigned n);

    // Constraint registration
    void add_eq(euf::snode* lhs, euf::snode* rhs, unsigned dep_id);
    void add_mem(euf::snode* str, euf::snode* regex, unsigned dep_id);
    void add_diseq(theory_var v1, theory_var v2);
};
```

Key design decisions:
- Use `scoped_vector` for backtrackable collections (same pattern as `theory_seq`)
- Map theory variables to snode representations via sgraph
- Dependency IDs correspond to `dep_tracker` bit positions for conflict explanation

### 5.3 Phase 3: Nielsen Transformation Algorithms

This is the core algorithmic phase. All additions go into `src/smt/seq/seq_nielsen.h/.cpp`.

#### 5.3.1 Simplification Engine

Add to `nielsen_node`:

```cpp
// In nielsen_node:
simplify_result simplify_and_init(nielsen_graph& g);
simplify_result simplify_str_eq(nielsen_graph& g, unsigned idx);
simplify_result simplify_str_mem(nielsen_graph& g, unsigned idx);
```

Simplification rules (matching ZIPT's `SimplifyAndInit`):
1. **Trivial equation removal**: If `lhs == rhs` (same snode), remove
2. **Empty propagation**: If `lhs = ε`, then `rhs` must be empty → conflict or propagate
3. **Constant prefix matching**: If both sides start with same character, strip it
4. **Constant mismatch**: If sides start with different characters → conflict (symbol_clash)
5. **Unit propagation**: If `x = c` where c is ground, substitute x→c everywhere
6. **Nullable regex**: If `str = ε` and regex is nullable → satisfied

#### 5.3.2 Modifier Chain

Add 13 modifiers matching ZIPT's priority order. Each modifier returns a list of `nielsen_edge` expansions:

```cpp
// In nielsen_graph:
struct modifier_result {
    ptr_vector<nielsen_edge> edges;
    bool deterministic;  // true if only one branch is valid
};

// Modifiers (in priority order):
modifier_result apply_det_modifier(nielsen_node& n);           // 1. Deterministic simplifications
modifier_result apply_power_epsilon(nielsen_node& n);          // 2. Power-epsilon: u="" || n=0
modifier_result apply_num_cmp(nielsen_node& n);                // 3. Numeric comparisons
modifier_result apply_const_num_unwinding(nielsen_node& n);    // 4. Constant power unwinding
modifier_result apply_eq_split(nielsen_node& n);               // 5. Equality prefix/suffix split
modifier_result apply_star_intr(nielsen_node& n);              // 6. Stabilizer introduction
modifier_result apply_gpower_intr(nielsen_node& n);            // 7. Power introduction
modifier_result apply_const_nielsen(nielsen_node& n);          // 8. Nielsen vs constant
modifier_result apply_regex_char_split(nielsen_node& n);       // 9. Regex character split
modifier_result apply_regex_var_split(nielsen_node& n);        // 10. Regex variable split
modifier_result apply_power_split(nielsen_node& n);            // 11. Power unwinding
modifier_result apply_var_nielsen(nielsen_node& n);            // 12. Variable Nielsen split
modifier_result apply_var_num_unwinding(nielsen_node& n);      // 13. Variable power unwinding
```

The modifier chain is applied in order; the first modifier that produces edges is used:

```cpp
modifier_result generate_extensions(nielsen_node& n) {
    modifier_result r;
    r = apply_det_modifier(n);        if (!r.edges.empty()) return r;
    r = apply_power_epsilon(n);       if (!r.edges.empty()) return r;
    // ... through all 13 modifiers
    r = apply_var_num_unwinding(n);
    return r;
}
```

#### 5.3.3 Graph Expansion & Iterative Deepening

Add to `nielsen_graph`:

```cpp
// Search result
enum class search_result { sat, unsat, unknown };

// Main search entry point
search_result solve();

// Iterative deepening DFS
search_result search_dfs(nielsen_node* node, unsigned depth);

// Expand a single node
search_result expand_node(nielsen_node* node, unsigned depth);
```

**Algorithm** (matching ZIPT's `NielsenGraph.Run()`):
1. Set initial depth bound (e.g., 10)
2. Run DFS from root with depth bound
3. If all branches conflict → UNSAT
4. If a leaf is satisfied (all constraints trivial) → SAT
5. If depth bound hit → increase bound, restart (iterative deepening)
6. Cap total iterations to prevent non-termination

#### 5.3.4 Subsumption Checking

Add to `nielsen_node`:

```cpp
bool is_subsumed_by(nielsen_node const& other) const;
```

A node N₁ is subsumed by N₂ if every constraint in N₂ also appears in N₁ (via snode pointer equality after canonicalization). Subsumption prevents exploring redundant branches.

#### 5.3.5 Conflict Detection & Explanation

Add to `nielsen_graph`:

```cpp
// Extract conflict explanation as a set of input constraint indices
void explain_conflict(nielsen_node const& conflict_node, svector<unsigned>& deps);
```

The `dep_tracker` bitvectors on each constraint track which original input constraints contributed. On conflict, OR together the dep_trackers of the conflicting constraints to get the minimal explanation.

### 5.4 Phase 4: Parikh Image / Length Reasoning

#### 5.4.1 Length Constraint Generation

For each word equation `lhs = rhs`, derive `|lhs| = |rhs|` as a linear arithmetic constraint. For each regex membership `x ∈ L(r)`, derive length bounds from the regex structure.

```cpp
// In nielsen_graph or a helper:
void generate_length_constraints(nielsen_node const& node,
                                 vector<expr_ref>& arith_constraints);
```

**Length computation from snode**:
- `|ε|` = 0
- `|c|` = 1 (character)
- `|a · b|` = `|a| + |b|`
- `|x^n|` = `n * |x|` (power)
- `|x|` = length variable for x

**Integration with arithmetic solver**: Use `arith_value` to query current length assignments and check feasibility. Propagate new length equalities/inequalities via `theory_nseq::propagate()`.

#### 5.4.2 Parikh Image (Advanced)

For regex membership `x ∈ L(r)`, extract Parikh constraints on the length:
- `x ∈ a*` → `|x| ≥ 0`
- `x ∈ a{3,5}` → `3 ≤ |x| ≤ 5`
- `x ∈ (ab)*` → `|x| mod 2 = 0`

Initially use simple interval-based reasoning from regex structure. Full PDD (Polynomial Decision Diagram) support from ZIPT can be deferred — use Z3's existing arithmetic solver for polynomial reasoning.

### 5.5 Phase 5: Regex Membership

#### 5.5.1 nseq_regex (`src/smt/nseq_regex.h/.cpp`)

Handles regex membership constraints using ZIPT's lazy approach:

```cpp
class nseq_regex {
    euf::sgraph&    m_sg;
    seq_rewriter&   m_rewriter;

    // Process regex membership after character consumption
    simplify_result process_str_mem(str_mem& mem, euf::snode* consumed_char);

    // Compute derivative and create new membership constraint
    str_mem derive(str_mem const& mem, euf::snode* char_node);

    // Check if regex is empty (unsatisfiable)
    bool is_empty_regex(euf::snode* regex);

    // Check for regex cycles (stabilizer introduction)
    bool detect_cycle(str_mem const& mem);

    // Compute minterms for character splitting
    void get_minterms(euf::snode* regex, vector<euf::snode*>& minterms);
};
```

**Lazy evaluation pattern** (per LazyMemberships.pdf):
- Only consume characters from the string when they become concrete (via substitution)
- Use Brzozowski derivatives: `D(c, r)` gives the derivative of regex `r` by character `c`
- Track history (consumed prefix) for cycle detection
- When a cycle is detected, introduce a stabilizer: `remaining ∈ base*`

**Reuse**: `sgraph::brzozowski_deriv()` and `sgraph::compute_minterms()` are already implemented.

### 5.6 Phase 6: Propagation Engine & Integration

#### 5.6.1 theory_nseq::final_check_eh()

The main solving loop:

```cpp
final_check_status theory_nseq::final_check_eh() {
    // 1. Collect constraints from SMT context into nielsen_graph
    m_nielsen.reset();
    populate_nielsen_graph();

    // 2. Run Nielsen search
    auto result = m_nielsen.solve();

    switch (result) {
    case search_result::sat:
        return FC_DONE;
    case search_result::unsat:
        // Extract conflict explanation
        svector<unsigned> deps;
        m_nielsen.explain_conflict(deps);
        // Build conflict clause from deps
        add_conflict_clause(deps);
        return FC_CONTINUE;
    case search_result::unknown:
        // Depth bound hit or timeout
        return FC_GIVEUP;
    }
}
```

#### 5.6.2 populate_nielsen_graph()

Convert active SMT constraints to nielsen_graph format:

```cpp
void theory_nseq::populate_nielsen_graph() {
    for (auto& eq : m_state.eqs()) {
        euf::snode* lhs = m_sgraph.mk(eq.first);
        euf::snode* rhs = m_sgraph.mk(eq.second);
        m_nielsen.add_str_eq(lhs, rhs);
    }
    for (auto& mem : m_state.mems()) {
        euf::snode* str = m_sgraph.mk(mem.str);
        euf::snode* regex = m_sgraph.mk(mem.regex);
        m_nielsen.add_str_mem(str, regex);
    }
}
```

#### 5.6.3 theory_nseq::propagate()

Propagate consequences from Nielsen solving to the SMT context:
- New equalities (from substitutions) → `ctx.assign_eq()`
- New disequalities → `ctx.assign_diseq()`
- New literals (regex memberships) → `ctx.assign()`
- Length constraints → `ctx.assign()` for arithmetic literals

### 5.7 Phase 7: Model Generation

#### 5.7.1 nseq_model (`src/smt/nseq_model.h/.cpp`)

Build concrete string values from solved Nielsen graph:

```cpp
class nseq_model {
    // Extract model assignments from a satisfied nielsen_node
    void extract_assignments(nielsen_node const& leaf,
                            obj_map<expr, expr*>& assignments);

    // Generate fresh string values for unconstrained variables
    expr_ref mk_fresh_value(sort* s, seq_factory& factory);

    // Ensure consistency with regex memberships
    bool validate_regex(expr* str_val, expr* regex);
};
```

**Model construction algorithm**:
1. From the satisfied leaf node, collect all substitutions along the path from root
2. Compose substitutions to get final variable assignments
3. For unconstrained variables, use `seq_factory::get_fresh_value()`
4. Register with `model_generator` via `init_model()` / `finalize_model()`

## 6. Alternatives Considered

| Option | Pros | Cons | Decision |
|--------|------|------|----------|
| Extend `theory_seq` with Nielsen | Single solver, shared infrastructure | Massive refactor, high risk to production solver | **Rejected**: Too risky to production |
| Port ZIPT as standalone user propagator | Minimal Z3 changes | Poor integration, no sharing of Z3 infrastructure, slower | **Rejected**: Misses optimization opportunities |
| New `theory_nseq` (selected) | Clean separation, reuses infrastructure, safe coexistence | New code to maintain, some duplication | **Selected**: Best balance of risk and benefit |
| PDD for Parikh (full ZIPT port) | Exact polynomial reasoning | Complex, Z3 has arithmetic solver already | **Deferred**: Use Z3 arithmetic initially, add PDD later if needed |

## 7. Cross-Cutting Concerns

### 7.1 Backtracking / Scope Management

`theory_nseq` must correctly implement `push_scope_eh()` / `pop_scope_eh()`:
- `nseq_state` uses `scoped_vector` (same as `theory_seq`)
- sgraph/egraph have their own `push()`/`pop()` — must be synchronized
- nielsen_graph is rebuilt from scratch on each `final_check_eh()` (no incremental state), so no backtracking needed for the graph itself

### 7.2 Conflict Clause Quality

Conflict explanations must be minimal for effective CDCL learning:
- `dep_tracker` bitvectors track which input constraints are responsible
- On conflict, extract the minimal set of input constraint IDs
- Map these back to Z3 literals for the conflict clause

### 7.3 Interaction with Arithmetic Solver

Length constraints create coupling between `theory_nseq` and the arithmetic solver:
- Use `arith_value` to query current arithmetic assignments (same pattern as `theory_seq`)
- Propagate derived length equalities as theory lemmas
- May need to handle `FC_CONTINUE` loops when arithmetic and string solvers ping-pong

### 7.4 Statistics

`collect_statistics()` should track:
- Number of Nielsen graph nodes explored
- Number of conflicts found
- Number of depth bound increases
- Number of regex derivatives computed
- Number of length constraints generated

## 8. Migration, Rollout, and Testing

### 8.1 Deployment Strategy

- [ ] Phase 1: `theory_nseq` returns `FC_GIVEUP` for all inputs — proves integration works
- [ ] Phase 2: Handle trivial word equations (constant strings, simple variables)
- [ ] Phase 3: Full modifier chain — handle the string regression suite
- [ ] Phase 4: Regex support — handle `re*.smt2` regression tests
- [ ] Phase 5: Performance tuning — compare against `theory_seq` on SMT-COMP benchmarks

### 8.2 Test Plan

#### Unit Tests (C++ tests in `src/test/`)

| Test | File | Scope |
|------|------|-------|
| `TST(nseq_basic)` | `src/test/nseq_basic.cpp` | theory_nseq instantiation, parameter selection, trivial sat/unsat |
| `TST(seq_nielsen)` | `src/test/seq_nielsen.cpp` (existing) | Extend with simplification, modifier, and search tests |
| `TST(euf_sgraph)` | `src/test/euf_sgraph.cpp` (existing) | Already passing; extend if sgraph changes are needed |

#### Regression Tests (SMT2 via z3 command line)

Use `C:\z3test\regressions\smt2\` (the same suite as nightly CI):

1. **String-specific files** with `smt.string_solver=nseq`:
   - `string-concat.smt2`, `string-eval.smt2`, `string-itos.smt2`, `string-literals.smt2`, `string-ops.smt2`, `string-simplify.smt2`
   - `string3.smt2`, `string6.smt2`, `string7.smt2`, `string9.smt2`, `string11.smt2`–`string14.smt2`
   - `re.smt2`, `re_rewriter.smt2`

2. **Comparison testing**: Run same files with both `smt.string_solver=seq` and `smt.string_solver=nseq`, verify sat/unsat agreement (no soundness bugs).

3. **Full regression suite**: Ensure `smt.string_solver=nseq` doesn't break non-string tests.

#### Targeted SMT2 Tests (New)

Create focused test files in `tests/nseq/`:
- `eq_basic.smt2` — Simple word equations
- `eq_nielsen.smt2` — Equations requiring Nielsen transformations
- `length.smt2` — Length constraints
- `regex.smt2` — Regex membership
- `mixed.smt2` — Combined string + arithmetic
- `unsat.smt2` — Unsatisfiable benchmarks

## 9. Design Decisions (Resolved)

- [x] **Q1: egraph ownership** — `theory_nseq` creates its own **private egraph/sgraph**, matching the ZIPT pattern where the string manager is independent. This avoids interference with other theories and keeps the string representation self-contained.

- [x] **Q2: Parikh implementation approach** — Use **Z3's existing arithmetic solver** via `arith_value` for length constraints. Generate linear length constraints from word equations and regex membership, propagate them as theory lemmas. ZIPT's PDD is deferred — Z3 already has a full arithmetic solver that theory_nseq can leverage directly.

- [x] **Q3: Nielsen graph persistence** — The Nielsen graph will be **maintained incrementally with backtracking support**. The graph persists across `final_check_eh()` calls with push/pop scope synchronization. This avoids redundant re-exploration of previously visited nodes when the SMT solver backtracks.

- [x] **Q4: Modifier chain completeness** — Implement an **essential subset of 5 modifiers first**: DetModifier, EqSplitModifier, ConstNielsenModifier, VarNielsenModifier, RegexCharSplitModifier. These cover basic word equations and simple regex membership. The remaining 8 modifiers (PowerEpsilon, NumCmp, ConstNumUnwinding, StarIntr, GPowerIntr, RegexVarSplit, PowerSplit, VarNumUnwinding) will be added incrementally in subsequent phases.

- [x] **Q5: Generic sequences** — `theory_nseq` handles **all `Seq[T]` types from the start**, not just strings. Nielsen transformations work on any element type. Regex membership is string-specific but the word equation engine is generic.

- [x] **Q6: Higher-order ops** — **Axiomatize minimally** for `seq.map`, `seq.mapi`, `seq.foldl`, `seq.foldli`. Generate basic axioms (similar to theory_seq's approach) without deep reasoning. This ensures theory_nseq doesn't immediately give up on problems containing these operations.

- [x] **Q7: Disequality handling** — Use **separate tracking like ZIPT**. Port ZIPT's character disequality and string disequality tracking into the nielsen_graph data structures. This gives the modifier chain direct access to disequality information (particularly needed for character minterm computation in RegexCharSplitModifier).

## 10. File Summary

### New Files

| File | Phase | Description |
|------|-------|-------------|
| `src/smt/theory_nseq.h` | 1 | Theory class header |
| `src/smt/theory_nseq.cpp` | 1 | Theory class implementation |
| `src/smt/nseq_state.h` | 2 | Constraint store header |
| `src/smt/nseq_state.cpp` | 2 | Constraint store implementation |
| `src/smt/nseq_regex.h` | 5 | Regex handling header |
| `src/smt/nseq_regex.cpp` | 5 | Regex handling implementation |
| `src/smt/nseq_model.h` | 7 | Model generation header |
| `src/smt/nseq_model.cpp` | 7 | Model generation implementation |
| `src/test/nseq_basic.cpp` | 1 | Unit tests |

### Files to Extend

| File | Phase | Change |
|------|-------|--------|
| `src/smt/seq/seq_nielsen.h` | 3 | Add simplification, modifier chain, search, subsumption methods |
| `src/smt/seq/seq_nielsen.cpp` | 3 | Implement above methods |

### Files to Modify (Integration)

| File | Phase | Change |
|------|-------|--------|
| `src/smt/smt_setup.h` | 1 | Declare `setup_nseq()` |
| `src/smt/smt_setup.cpp` | 1 | Add `"nseq"` dispatch, implement `setup_nseq()` |
| `src/params/smt_params.cpp` | 1 | Add `"nseq"` to `validate_string_solver()` |
| `src/params/smt_params_helper.pyg` | 1 | Document `nseq` option |
| `src/smt/CMakeLists.txt` | 1 | Add new .cpp files to SOURCES |
| `src/test/main.cpp` | 1 | Register `TST(nseq_basic)` |
| `src/test/CMakeLists.txt` | 1 | Add `nseq_basic.cpp` |

## 11. Implementation Order

1. **Phase 1** — Skeleton (`theory_nseq` class, parameter integration, build system) — compilable stub returning `FC_GIVEUP`
2. **Phase 2** — State management (`nseq_state`) — constraint store with backtracking
3. **Phase 3** — Nielsen algorithms (simplification, modifiers, search, subsumption, conflict) — core solver
4. **Phase 4** — Length/Parikh reasoning — arithmetic integration
5. **Phase 5** — Regex membership (`nseq_regex`) — lazy derivatives
6. **Phase 6** — Propagation wiring — connect all components in `final_check_eh`
7. **Phase 7** — Model generation (`nseq_model`) — satisfying assignments
