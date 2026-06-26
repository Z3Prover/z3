# Range-Set Integration — Handoff Plan

Status: **planning / clean slate**
Branch: `veanes/range-set-integration` (based on `master`)
Author of range-set infrastructure: Margus Veanes (`veanes`), 2026

This document is the starting point for follow-up work on tighter integration of
range-sets into the regex/sequence solver. It summarizes the current state in
`master` (after the "Derive with ranges" merge, PR #9965), lays out the two
candidate integration approaches we discussed (the invasive `re.ranges` AST node
vs. an internal-only deepening), and gives a concrete evaluation plan so the
branch can be measured against `master` on the same benchmarks used during the
derivative work.

---

## 1. Current state in `master` (baseline)

The "Derive with ranges" work already landed a self-contained range-set value
type and a translator, but **range-sets are not first-class in the regex AST**.
They live only as a transient internal representation at the smart-constructor
boundary.

### 1.1 `range_predicate` — the range-set value type
- Files: `src/ast/rewriter/seq_range_predicate.h`, `seq_range_predicate.cpp`
- A canonical subset of the unsigned character domain `[0, max_char]`, stored as
  a sorted vector of disjoint, non-adjacent ranges `[(lo_0,hi_0), ...]` with
  `hi_i + 1 < lo_{i+1}`.
- Canonical: two predicates over the same domain are extensionally equal iff
  their internal vectors are elementwise equal.
- Full Boolean algebra, all linear in the number of ranges:
  `operator| & - ^ ~`, plus `empty/top/singleton/range`, `contains`,
  `cardinality`, `equals`, `operator<`, `hash`, `display`.
- **Pure value**: no `ast_manager` allocation in construction or Boolean ops.
  Conversion to/from `expr*` is delegated to a separate translator.

### 1.2 `seq_range_collapse` — the regex <-> range_predicate translator
- Files: `src/ast/rewriter/seq_range_collapse.h`, `seq_range_collapse.cpp`
- `regex_to_range_predicate(u, r, out)`: recognizes the
  **boolean-combination-of-ranges** fragment
  (`re.empty`, `re.allchar`, `re.range`, `re.union`, `re.inter`, `re.diff`, and
  `inter` with a `complement` operand → difference) and folds it into a
  canonical `range_predicate`. Returns `false` (caller falls back to the generic
  path) for anything outside the fragment.
- `range_predicate_to_regex(u, p, seq_sort)`: **materializes** a predicate back
  into AST as a right-associated union of single `re.range` nodes, **sorted by
  expression id** to match the canonical shape `seq_rewriter::merge_regex_sets`
  expects.

### 1.3 Where it is used today (the only integration point)
- `src/ast/rewriter/seq_rewriter.cpp`, smart constructors:
  - `try_collapse_re_union` (~3690): `pa | pb`
  - `try_collapse_re_inter` (~3703): `pa & pb`
  - `try_collapse_re_diff`  (~3866): `pa - pb`
- Pattern in each: collapse both operands to `range_predicate`, run the Boolean
  op on the value type, materialize back to AST. If either operand is outside the
  fragment, bail out and use the generic regex constructor.
- **`seq_derive.cpp` does not use `range_predicate` directly** — the derivative
  engine still works over regex AST + ITE path conditions; range-sets only touch
  the union/inter/diff smart constructors.

### 1.4 Latent AST vehicle already present
- `OP_RE_RANGE` (`re.range`): the single-range character class.
- `OP_RE_OF_PRED` (`re.of.pred`, `is_of_pred`): a regex that accepts a **single
  character satisfying a predicate** — already declared and signed in
  `seq_decl_plugin.cpp` (sig at ~240, build at ~1206, nullable/printer cases at
  ~410/1111/1694). This is the natural existing hook for a first-class
  character-class / range-set node.

### 1.5 Key invariants that any integration MUST preserve
- **Soundness**: 0 sat/unsat mismatches vs `master` on the corpus (this held
  through all derivative work; it is the gate).
- **Domain guard**: the range algebra only models length-1 character classes
  over `[0, max_char]`. Reject non-string regex element sorts up front (see
  `regex_to_range_predicate` guard) — never fabricate a char-class for a regex
  over `(Seq Int)` etc.
- **`re.complement` is sequence-level, not character-level.** Its language
  includes `epsilon`, length >= 2 strings, and length-1 strings outside the
  operand. It must **not** be collapsed to char-level `~`. De-Morgan / empty /
  full special cases are handled in `mk_re_complement`. (See the long NOTE in
  `seq_range_collapse.cpp`.)
- **Canonical id-sorted union shape** on materialization, or
  `merge_regex_sets` produces wrong unions.
- **Derivative-kind gating** (from prior work, now in `master`): intersection-
  over-union and concat-over-union distribution are gated on
  `derivative_kind::antimirov_t`; brzozowski mode (used by `regex_bisim` and the
  emptiness enumeration) keeps intersections above unions. Do not regress this.

---

## 2. Candidate approaches

### Approach A — first-class `re.ranges` node (most invasive)
Make a range-set a single regex AST node, either by introducing a new internal
op (e.g. `_OP_RE_RANGES`) or by **reusing `OP_RE_OF_PRED`** with a range-set
encoded predicate so a length-1 character class is one node carrying a
`range_predicate` (or a canonical predicate term).

Potential benefits:
- Eliminates the repeated collapse <-> materialize round-trips; a char class is
  created, hashed, and shared **once**.
- Removes the union-of-`re.range` blowup in the stored AST: one node instead of
  N union leaves; structural sharing + hash-consing give O(1) equality on char
  classes.
- Derivative head conditions / OneStep predicates become single nodes; bisim and
  emptiness compare char classes by pointer/hash instead of walking unions.
- Cleaner normal form: `union`/`inter`/`diff`/`complement` of char classes fold
  into the node directly.

Costs / risks (this is the invasive part):
- Touches every site that pattern-matches the regex AST: `seq_rewriter`,
  `seq_derive`, `seq_regex` (theory), `seq_decl_plugin` (nullable, derivative,
  pretty-printer, well-formedness), `sls_seq_plugin`, NNF/translation, model
  construction, and any `is_union`/`is_range` matcher that currently assumes the
  union-of-ranges shape.
- Needs nullable + derivative rules for the new node (a length-1 class is never
  nullable; its derivative wrt `c` is `epsilon` if `c in set` else `empty`).
- Sub-decision: **internal-only** (never exposed to SMT-LIB / API / models;
  rewritten away at the boundary) vs **fully exposed** (parser, printer,
  proofs, model values, API, pretty-printing all updated). Internal-only is
  strongly preferred as the first step — much smaller blast radius.

### Approach B — deepen internal range-set use, keep it out of the AST (least invasive)
Keep `range_predicate` as a transient value type (no AST node), but use it in
more places and cache it harder.

Possible moves:
- Memoize `regex_to_range_predicate` results keyed on `expr*` id so the collapse
  cost is paid once per char-class subterm.
- Use `range_predicate` for the char-class arithmetic inside derivative path
  conditions / OneStep instead of building ITE/union AST and re-collapsing.
- Extend the recognized fragment (carefully — respecting the `re.complement`
  caveat) and short-circuit more constructor cases through the value type.

Benefits: low risk, incremental, no AST/API/printer/model changes, all existing
matchers keep working; easy to land and measure piecewise.
Costs: the collapse/materialize cost at the AST boundary remains; the
union-of-ranges blowup still exists in any AST that is stored or compared
structurally (bisim/emptiness still walk unions).

### Recommended phasing
1. Land Approach B's caching/memoization first as a **measurable baseline** — it
   is cheap and de-risks the corpus.
2. Prototype Approach A **internal-only via `OP_RE_OF_PRED`** on the single
   hottest path (derivative char-class conditions or the union/inter/diff
   constructor output), keeping it rewritten-away at the SMT-LIB/API boundary.
3. Only consider full exposure (parser/printer/model/API) if the internal-only
   prototype shows a clear, sustained win on the corpus.

---

## 3. Evaluation plan

Goal: measure this branch against `master` on the **same** benchmarks used during
the derivative work, with **soundness as the gate** (0 mismatches).

### 3.1 Benchmarks
- **Regex-equivalence corpus**: `C:\git\bench\inputs\regex-equivalence`
  (1523 `.smt2` files). Key sub-dirs: `cade29[_equiv]\parametric`,
  `cade29[_equiv]\boolean_and_loops`, `mutations[_equiv]`,
  `realworld\{email,url,snort}`.
- **QF_S**: `C:\git\bench\inputs\QF_S` (e.g. `20230329-automatark-lu`,
  `20230329-woorpje-lu`, `20240318-omark`, `2019-Jiang`, ...).

### 3.2 Harness (already present, untracked)
- `C:\git\z3\.regtests\run_branch_only.ps1` — runs one solver over a directory,
  emits CSV `file, branch_result, branch_ms`. Param: `-Out <csv>` (NOT
  `-OutCsv`), `-Timeout <sec>` (default 10), `-Dir <path>`.
- `C:\git\z3\.regtests\run_regex_equiv.ps1` — runs both solvers, emits
  `file, branch_res, branch_ms, master_res, master_ms, status`.
- Baseline `master` numbers do not change — reuse the cached master columns
  rather than re-running master.

### 3.3 Metric / comparison method (proven during derivative work)
- Normalize verdicts to `sat` / `unsat` / `to` (timeout/unknown/empty/error
  annotations stripped) before comparing — CSV-quoting of `(error ...)` self-
  check noise from mutation benchmarks otherwise causes false MISMATCH.
- Report:
  - **branch-only timeouts vs master** (branch times out, master solves) — the
    primary regression signal,
  - **branch wins** (master times out, branch solves),
  - **soundness mismatches** — must be **0**.
- Reference numbers from the derivative branch at hand-off
  (regex-equivalence, 10s timeout): the shipped config had **14** branch-only
  timeouts and **13** branch wins vs master, 0 mismatches. Use that as the bar
  to beat; a range-set change should not increase branch-only timeouts.

### 3.4 Build (Windows / CMake + Ninja)
```
& $env:ComSpec /c 'call "C:\Program Files\Microsoft Visual Studio\2022\Enterprise\VC\Auxiliary\Build\vcvars64.bat" >nul && cd /d C:\git\z3\build\release && ninja shell test-z3'
```
Unit tests: `C:\git\z3\build\release\test-z3.exe /a` (expect all pass).
(The `'vswhere.exe' is not recognized` warning is harmless.)

### 3.5 Procedure
1. Build `shell` + `test-z3`; `test-z3 /a` green.
2. `run_branch_only.ps1` over `regex-equivalence` -> CSV; compare to cached
   master baseline with the normalized-verdict comparison.
3. Repeat over a QF_S subset (start with `20230329-automatark-lu`).
4. Gate: 0 mismatches; branch-only timeouts <= 14 on regex-equivalence.
5. Spot-check the historically hard cases: `flat_vs_loop_018_n20`,
   `det_blowup_024` (direct + equiv), a few `mut_*` sat cases, and the
   `5721/5728/5731` regressions.

---

## 4. Pointers / file index

| Area | File | Notes |
| --- | --- | --- |
| Range-set value type | `src/ast/rewriter/seq_range_predicate.{h,cpp}` | canonical Boolean algebra, no AST alloc |
| Translator | `src/ast/rewriter/seq_range_collapse.{h,cpp}` | regex <-> range_predicate, fragment + caveats |
| Constructor integration | `src/ast/rewriter/seq_rewriter.cpp` ~3690/3703/3866 | `try_collapse_re_{union,inter,diff}` |
| Derivative engine | `src/ast/rewriter/seq_derive.{cpp,h}` | derivative-kind gating; no range_predicate yet |
| Bisim | `src/ast/rewriter/seq_regex_bisim.cpp` | brzozowski cofactors |
| Theory | `src/smt/seq_regex.cpp` | emptiness/membership, `get_derivative_targets` |
| AST ops | `src/ast/seq_decl_plugin.{h,cpp}` | `OP_RE_RANGE`, `OP_RE_OF_PRED` (`is_of_pred`) |

---

## 5. Open questions for the author
- For Approach A: new internal `_OP_RE_RANGES` op, or reuse `OP_RE_OF_PRED` with
  a range-set predicate? (Reuse minimizes new surface; a dedicated op is clearer
  and lets `range_predicate` ride directly.)
- Internal-only first (rewritten away at the boundary), or commit to full
  SMT-LIB/API/model exposure?
- How invasive is acceptable for the bisim/emptiness comparison path — is a
  pointer/hash equality on char classes worth the AST churn?
- Which is the single hottest path to prototype on (derivative char-class
  conditions vs. constructor output)?
