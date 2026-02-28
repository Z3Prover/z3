# Implementation Plan: theory_nseq — New String Theory Solver for Z3

## Problem Statement

Implement a new theory solver `theory_nseq` for strings/sequences in Z3's SMT solver framework (`src/smt/`). The solver is based on the algorithms described in **LazyMemberships.pdf** and **ClemensTableau.pdf**, with a reference C# implementation at [ZIPT](https://github.com/CEisenhofer/ZIPT/tree/parikh/ZIPT). The new solver should coexist with the existing `theory_seq` and be selectable via the `smt.string_solver` parameter.

## Reference Architecture

The ZIPT reference implementation (C#) contains these key components:
- **StringPropagator** — core constraint propagation engine
- **Nielsen Graph/Node/Edge** — word equation solving via Nielsen transformations
- **Constraint system** — StrEq, StrMem (regex membership), StrContains, prefix/suffix, disequalities
- **Modifier chain** — decomposition, equation splitting, Nielsen transforms, regex splitting
- **IntUtils (PDD, Interval)** — Parikh image / integer constraint reasoning for lengths
- **StrManager** — string state tracking, canonicalization

## Approach

Build `theory_nseq` as a new theory plugin in `src/smt/`, following the same patterns as `theory_seq`. Reuse existing Z3 infrastructure (seq_decl_plugin, seq_rewriter, seq_skolem, arith_value) and add new algorithm-specific modules. Self-contained rewriter utilities go in `src/ast/rewriter/`.

---

## Module Breakdown

### Phase 1: Skeleton & Integration

#### 1.1 theory_nseq skeleton (`src/smt/theory_nseq.h`, `src/smt/theory_nseq.cpp`)
- New class `theory_nseq : public theory`
- Implement all required virtual methods from `smt::theory`:
  - `internalize_atom`, `internalize_term`
  - `new_eq_eh`, `new_diseq_eh`, `assign_eh`
  - `can_propagate`, `propagate`
  - `final_check_eh`
  - `push_scope_eh`, `pop_scope_eh`
  - `mk_fresh`, `get_name` (return `"nseq"`)
  - `mk_value`, `init_model`, `finalize_model`
  - `display`, `collect_statistics`
- Initially stub all methods (FC_GIVEUP on final_check)
- Use `seq_util` and `arith_util` from existing infrastructure
- Hold references to `seq_rewriter`, `seq::skolem`, `arith_value`

#### 1.2 Parameter integration
- **`src/params/smt_params_helper.pyg`**: Add `'nseq'` to string_solver options documentation
- **`src/params/smt_params.cpp`**: Add `"nseq"` to `validate_string_solver()`
- **`src/smt/smt_setup.cpp`**: Add `"nseq"` case in `setup_QF_S()` and `setup_seq_str()`, calling new `setup_nseq()` method
- **`src/smt/smt_setup.h`**: Declare `setup_nseq()`

#### 1.3 Build system integration
- **`src/smt/CMakeLists.txt`**: Add `theory_nseq.cpp` and all new `.cpp` files to SOURCES

### Phase 2: Core Data Structures

#### 2.1 String representation & state management (`src/smt/nseq_state.h/.cpp`)
- String variable tracking (analogous to ZIPT's StrManager)
- Concatenation decomposition into token sequences
- Canonicalization of string terms
- Variable-to-representative mapping (union-find or solution map)
- Backtrackable state via `scoped_vector` / trail

#### 2.2 Constraint representation (`src/smt/nseq_constraint.h`)
- Constraint types: StrEq, StrNe, StrMem (regex membership), StrContains, StrPrefix, StrSuffix
- IntEq, IntLe, IntNe for length constraints
- Dependency tracking for conflict explanations
- Constraint simplification results

#### 2.3 Dependency tracker (`src/smt/nseq_dep.h/.cpp`)
- Track justifications for derived facts
- Integrate with Z3's `scoped_dependency_manager<assumption>` pattern (same as theory_seq)
- Support linearization for conflict clause generation

### Phase 3: Word Equation Solver (Nielsen Transformations)

#### 3.1 Nielsen graph (`src/ast/rewriter/nseq_nielsen.h/.cpp`)
- Nielsen transformation graph: nodes represent equation states, edges represent transformations
- Node: stores a set of simplified word equations
- Edge: transformation applied (variable elimination, constant matching, split)
- Graph exploration with cycle detection
- Self-contained rewriter utility (no dependency on smt context)

#### 3.2 Nielsen node operations
- **Constant matching**: if both sides start with same constant, strip it
- **Variable elimination**: if LHS starts with variable x, case-split: x=ε or x=a·x' 
- **Equation decomposition**: split compound equations
- **Determinism detection**: identify forced assignments
- **Directed Nielsen**: apply transformations in a directed manner

#### 3.3 Modifier chain (integrated into nielsen module)
- DecomposeModifier — decompose strings into concatenation components
- EqSplitModifier — case analysis on equalities
- VarNielsenModifier / ConstNielsenModifier / DirectedNielsenModifier
- StarIntrModifier — Kleene star introduction/elimination
- PowerSplitModifier / PowerEpsilonModifier
- RegexCharSplitModifier / RegexVarSplitModifier

### Phase 4: Length Constraint Integration (Parikh Image)

#### 4.1 Length reasoning (`src/ast/rewriter/nseq_length.h/.cpp`)
- Interval arithmetic for length bounds
- Length variable management
- Integration with Z3's arithmetic solver via `arith_value`
- Parikh image constraints: derive integer constraints from string equations
- Self-contained rewriter utility

#### 4.2 Arithmetic interface in theory_nseq
- Query arithmetic solver for current length assignments
- Propagate length equalities/inequalities derived from string equations
- Use `arith_value` (same pattern as theory_seq)

### Phase 5: Regex Membership

#### 5.1 Regex handling (`src/smt/nseq_regex.h/.cpp`)
- Lazy membership checking (per LazyMemberships.pdf)
- Regex derivative computation (reuse `seq_rewriter.mk_derivative`)
- Regex splitting for equation solving
- Integration with Nielsen transformations
- Nullable checking

### Phase 6: Propagation Engine

#### 6.1 String propagator (`src/smt/nseq_propagator.h/.cpp`)
- Main propagation loop integrating all components
- Equation simplification pipeline
- Constraint interaction (string eq + length + regex)
- Case splitting decisions
- Conflict detection and clause generation

#### 6.2 Wire into theory_nseq
- `internalize_term/atom`: register string terms, create theory variables, enqueue axioms
- `assign_eh`: process boolean assignments (e.g., regex memberships, contains)
- `new_eq_eh/new_diseq_eh`: process equality/disequality merges
- `propagate`: run propagation engine
- `final_check_eh`: comprehensive consistency check, case splits

### Phase 7: Model Generation

#### 7.1 Model construction
- Build string values from solved equations
- Handle unconstrained variables
- Generate models consistent with length constraints and regex memberships
- Register `seq_factory` for value generation

---

## Testing Plan

### Unit Tests

#### T1: Basic smoke test (`src/test/nseq_basic.cpp`)
- Register test in `src/test/main.cpp` via `TST(nseq_basic)`
- Test that theory_nseq can be selected via `smt.string_solver=nseq`
- Verify basic sat/unsat on trivial string equalities

#### T2: Nielsen transformation tests
- Unit tests for the Nielsen graph/node rewriter module
- Test constant matching, variable elimination, equation decomposition

#### T3: Length reasoning tests
- Test interval propagation, Parikh image constraint generation

### Integration Tests (via z3 command line)

#### T4: z3test regression benchmarks (local at `C:\z3test`)
The z3test repository is available locally at `C:\z3test`. It contains the same regression suite used by nightly CI (`.github/workflows/nightly.yml:198`).

**Key string/regex benchmarks in `C:\z3test\regressions\smt2`:**
- `string-concat.smt2`, `string-eval.smt2`, `string-itos.smt2`, `string-literals.smt2`, `string-ops.smt2`, `string-simplify.smt2`
- `string3.smt2`, `string6.smt2`, `string7.smt2`, `string9.smt2`, `string11.smt2` through `string14.smt2`
- `re.smt2`, `re_rewriter.smt2`
- `testfoldl.smt2`, `testmap.smt2`, `testmapi.smt2` (sequence higher-order)
- `byte_string.smt2` (disabled)

**Testing approach:**
1. Run full regression suite: `python C:\z3test\scripts\test_benchmarks.py <z3exe> C:\z3test\regressions\smt2`
   - The test harness runs each `.smt2` file with `model_validate=true` and compares output to `.expected.out`
   - Script supports parallel execution (uses all CPU cores by default)
2. Run string-specific subset with `smt.string_solver=nseq`:
   - For each `string*.smt2` and `re*.smt2` in `C:\z3test\regressions\smt2`, run: `z3 smt.string_solver=nseq <file>`
   - Compare output against `.expected.out` files
3. Also test `C:\z3test\regressions\issues` (8 issue-specific regression tests)

**Other regression directories to verify (non-string, but ensure no regressions):**
- `C:\z3test\regressions\smt2-extra`
- `C:\z3test\regressions\smt2-debug`

#### T5: Targeted string SMT2 tests
Create focused test files exercising specific features:
- `tests/nseq/eq_basic.smt2` — simple word equations (x·a = a·x)
- `tests/nseq/eq_nielsen.smt2` — equations requiring Nielsen transformations
- `tests/nseq/concat.smt2` — concatenation reasoning
- `tests/nseq/contains.smt2` — str.contains, str.prefixof, str.suffixof
- `tests/nseq/length.smt2` — length constraints and Parikh image
- `tests/nseq/regex.smt2` — regex membership
- `tests/nseq/mixed.smt2` — combinations of string ops with arithmetic
- `tests/nseq/unsat.smt2` — unsatisfiable benchmarks

#### T6: Comparison testing with parallel runner
- Use `~/dev/test_scripts/src/run_in_parallel.py` for parallel testing
- Run the same SMT files with both `smt.string_solver=seq` and `smt.string_solver=nseq`
- Verify no soundness bugs (sat/unsat agree)

### Performance Testing

#### T7: Performance benchmarks (release builds only)
- Use SMT-COMP string benchmarks (QF_S, QF_SLIA tracks)
- Compare solve times between theory_seq and theory_nseq
- Use `z3 -st` for statistics
- **Only on release builds** (never debug builds)

---

## File Summary

### New files to create:
| File | Description |
|------|-------------|
| `src/smt/theory_nseq.h` | Theory class header |
| `src/smt/theory_nseq.cpp` | Theory class implementation |
| `src/smt/nseq_state.h` | String state management header |
| `src/smt/nseq_state.cpp` | String state management impl |
| `src/smt/nseq_constraint.h` | Constraint type definitions |
| `src/smt/nseq_dep.h` | Dependency tracking header |
| `src/smt/nseq_dep.cpp` | Dependency tracking impl |
| `src/smt/nseq_propagator.h` | Propagation engine header |
| `src/smt/nseq_propagator.cpp` | Propagation engine impl |
| `src/smt/nseq_regex.h` | Regex handling header |
| `src/smt/nseq_regex.cpp` | Regex handling impl |
| `src/ast/rewriter/nseq_nielsen.h` | Nielsen transformation header |
| `src/ast/rewriter/nseq_nielsen.cpp` | Nielsen transformation impl |
| `src/ast/rewriter/nseq_length.h` | Length/Parikh reasoning header |
| `src/ast/rewriter/nseq_length.cpp` | Length/Parikh reasoning impl |
| `src/test/nseq_basic.cpp` | Unit tests |

### Existing files to modify:
| File | Change |
|------|--------|
| `src/smt/smt_setup.h` | Declare `setup_nseq()` |
| `src/smt/smt_setup.cpp` | Add `"nseq"` to string_solver dispatch, implement `setup_nseq()` |
| `src/smt/CMakeLists.txt` | Add new .cpp files |
| `src/ast/rewriter/CMakeLists.txt` | Add new rewriter .cpp files |
| `src/params/smt_params_helper.pyg` | Document `nseq` option |
| `src/params/smt_params.cpp` | Add `"nseq"` to validation |
| `src/test/main.cpp` | Register `TST(nseq_basic)` |
| `src/test/CMakeLists.txt` | Add `nseq_basic.cpp` (if needed) |

---

## Implementation Order

1. **Phase 1** (Skeleton & Integration) — get a compilable stub that Z3 can load
2. **Phase 2** (Core Data Structures) — state management and constraint representation
3. **Phase 3** (Nielsen Transformations) — core word equation solving
4. **Phase 4** (Length/Parikh) — arithmetic integration
5. **Phase 5** (Regex) — regex membership
6. **Phase 6** (Propagation Engine) — wire everything together
7. **Phase 7** (Model Generation) — produce satisfying assignments
8. **Testing** — runs in parallel with each phase; benchmarks after Phase 6

## Notes

- The ZIPT C# reference at `github.com/CEisenhofer/ZIPT` (parikh branch) is the primary algorithm reference
- LazyMemberships.pdf describes the lazy regex membership approach
- ClemensTableau.pdf describes additional algorithms
- Reuse Z3 infrastructure wherever possible: `seq_util`, `seq_rewriter`, `seq_skolem`, `arith_value`, `seq_factory`
- Self-contained utilities (Nielsen graph, length reasoning) go in `src/ast/rewriter/` per the spec
- All timing-sensitive builds require 30+ minute timeouts
