# F* Formalization of `src/ast/rewriter/bv_rewriter.cpp` — Coverage Report

See [`README.md`](README.md) for the top-level index of this F*
formal-verification audit series.

`bv_rewriter.cpp` (3153 lines, ~90 `mk_*`/helper functions) is Z3's
bit-vector term simplifier: given an applied bit-vector operator and its
(already-simplified) arguments, it either folds numeral arguments, applies a
structural identity, or gives up (`BR_FAILED`). This is the **first pass**
of a planned multi-stage effort (bit-vectors → datatypes → arrays/other
`th_rewriter.cpp` plugins → `ast/simplifiers` preprocessors); it establishes
the semantic model and proves the core defining identities and a
representative set of structural rewrites. Coverage is intentionally
*broad-but-shallow*: the many search/heuristic rewrites bv_rewriter.cpp uses
to simplify equations and inequalities between sums/concats are catalogued
below as not-yet-covered, to be addressed in follow-up passes.

Proof files:
[`Z3BvTheory.fst`](Z3BvTheory.fst) (semantics) and
[`Z3BvRewriter.fst`](Z3BvRewriter.fst) (rewrite-rule lemmas).

Toolchain used: [F*](https://github.com/FStarLang/FStar) `v2026.09.27`
(Windows x64) with Z3 `4.13.3` as the SMT backend. Both files type-check and
discharge all verification conditions with **no `admit`/`assume`/axioms**:

```
C:\fstar\fstar\bin\fstar.exe --smt C:\z3-4.13.3\z3-4.13.3-x64-win\bin\z3.exe Z3BvTheory.fst
C:\fstar\fstar\bin\fstar.exe --smt C:\z3-4.13.3\z3-4.13.3-x64-win\bin\z3.exe Z3BvRewriter.fst
```

## Representation (`Z3BvTheory.fst`)

A width-`n` bit-vector is modeled as `FStar.UInt.uint_t n`, i.e. a natural
number `0 <= x < 2^n` — the same "numeral mod `2^n`" representation
`bv_rewriter.cpp`/`bv_util` itself uses internally (`rational` value +
`size`). Bitwise and arithmetic operations (`bvand`/`bvor`/`bvxor`/`bvnot`/
`bvadd`/`bvsub`/`bvmul`/`bvneg`/`bvshl`/`bvlshr`/`rotate_left`/`rotate_right`/
`zero_extend`) are defined as *literally* the corresponding `FStar.UInt`
functions, so every algebraic/shift/rotate lemma already proved in that
library (commutativity, associativity, self-identities, `shift_*_value_lemma`,
`rotate_*_lemma`, `rotate_*_full_identity`, ...) applies to our operations
with no extra proof burden. Operations without a direct library counterpart
are defined from first principles as plain `nat`/`int` arithmetic:

| Operation | Definition | Rationale |
|---|---|---|
| `bvudiv`/`bvurem` | SMT-LIB2 total convention (div-by-zero → all-ones / dividend) | matches `mk_bv_udiv_i`/`mk_bv_urem_i` |
| `bvashr` | `NOT(logical-shift-right(NOT a, s))` | standard sign-replication identity |
| `to_int_signed`/`msb` | two's-complement interpretation | needed for `slt`/`sle`/`sdiv`/... |
| `bv_extract hi lo a` | `(a / 2^lo) % 2^(hi-lo+1)` | matches `mk_extract`/`OP_EXTRACT` |
| `bv_concat a b` | `a * 2^m + b` | matches `OP_CONCAT` (`a` in high bits) |
| `bv_zero_extend`/`bv_sign_extend` | reuse `FStar.UInt.zero_extends`; sign-extend via double-complement | matches `mk_zero_extend`/`mk_sign_extend` |
| `bv_ult`/`bv_ule`/`bv_slt`/`bv_sle` | nat / signed-int comparison | matches `mk_ule`/`mk_sle` family |
| `bv_redor`/`bv_redand`/`bv_comp` | definitional | matches `OP_BREDOR`/`OP_BREDAND`/`OP_BCOMP` |

## Coverage by rewrite rule (`Z3BvRewriter.fst`)

| bv_rewriter.cpp site | Rewrite | Lemma | Status |
|---|---|---|---|
| `mk_bv_and` | `x AND x = x` | `lemma_bvand_self` | ✅ |
| `mk_bv_and` | `x AND 0 = 0` | `lemma_bvand_zero` | ✅ |
| `mk_bv_and` | `x AND 11..1 = x` | `lemma_bvand_ones` | ✅ |
| `mk_bv_or` | `x OR x = x` | `lemma_bvor_self` | ✅ |
| `mk_bv_or` | `x OR 0 = x` | `lemma_bvor_zero` | ✅ |
| `mk_bv_or` | `x OR 11..1 = 11..1` | `lemma_bvor_ones` | ✅ |
| `mk_bv_xor` | `x XOR x = 0` | `lemma_bvxor_self` | ✅ |
| `mk_bv_xor` | `x XOR 0 = x` | `lemma_bvxor_zero` | ✅ |
| `mk_bv_not` (`m_bvnot_simpl`) | `NOT(NOT x) = x` | `lemma_bvnot_involutive` | ✅ |
| `mk_bv_nand`/`mk_bv_nor`/`mk_bv_xnor` | definitions via `NOT`∘`AND`/`OR`/`XOR` | `lemma_bvnand_def`/`lemma_bvnor_def`/`lemma_bvxnor_def` | ✅ (definitional) |
| `mk_bv_add` | `x + 0 = x` | `lemma_bvadd_zero` | ✅ |
| `mk_sub` | `x - x = 0` | `lemma_bvsub_self` | ✅ |
| `mk_sub` | `x - y = x + (-y)` | `lemma_bvsub_is_add_neg` | ✅ |
| `mk_bv_mul` | `x * 0 = 0`, `x * 1 = x` | `lemma_bvmul_zero`, `lemma_bvmul_one` | ✅ |
| `mk_uminus` | `-(-x) = x`, `-0 = 0` | `lemma_bvneg_involutive`, `lemma_bvneg_zero` | ✅ |
| `mk_bv_shl`/`mk_bv_lshr`/`mk_bv_ashr` | shift-by-0 = identity | `lemma_bvshl_zero`, `lemma_bvlshr_zero`, `lemma_bvashr_zero` | ✅ |
| `mk_bv_shl`/`mk_bv_lshr` | shift-by-`>=n` = `0` | `lemma_bvshl_overflow`, `lemma_bvlshr_overflow` | ✅ |
| `mk_bv_rotate_left`/`_right` | rotate-by-`n` = identity | `lemma_rotate_left_full`, `lemma_rotate_right_full` | ✅ |
| `mk_extract` | full-range extract = identity | `lemma_extract_full` | ✅ |
| `mk_extract` | nested extract composes | `lemma_extract_extract` | ✅ |
| `mk_extract`/`propagate_extract` | split-then-reconcatenate reconstructs the original value | `lemma_concat_extract_reconstruct` | ✅ |
| `mk_extract` | extract distributes over `NOT`/`OR`/`XOR` | — | ❌ deferred (follow-up pass) |
| `mk_zero_extend` | `k = 0` is identity | `lemma_zero_extend_zero` | ✅ |
| `mk_sign_extend` | `k = 0` is identity | `lemma_sign_extend_zero` | ✅ |
| `mk_ult`, `mk_slt` | defined via `NOT ∘ mk_ule`/`mk_sle` | `lemma_ult_def`, `lemma_slt_def` | ✅ |
| `mk_leq_core` (`is_zero_extended` fast path) | `(zero_extend x) <=_s (zero_extend y) == x <=_u y` | `lemma_sle_zero_extend` | ✅ |
| numeral folding (every `mk_*` operator's numeral/numeral or all-numeral-args branch) | — | sound by construction: `Z3BvTheory`'s functions *are* the functions the fold evaluates | N/A — see note below |

### Note on constant folding

Every `mk_*` function's numeral-folding branch (e.g. `mk_bv_add` summing
numeral arguments, `mk_extract` computing `(v >> low) & mask` on a numeral)
is not a separate algebraic fact to prove: bv_rewriter.cpp's numeral case
*is* an evaluation of the same function `Z3BvTheory.fst` models
(`bvadd`/`bv_extract`/...), so its soundness follows directly from the
semantic definitions themselves, not from a side lemma.

## Not yet covered (deferred to follow-up passes)

These are heuristic/search rewrites rather than single reusable identities;
following the convention of the sibling `ARITH`/`SEQ_REWRITER` reports, they
are catalogued here as explicitly out of scope for this pass rather than
silently skipped:

- `rw_leq_overflow`, `rw_leq_concats`, `are_eq_upto_num` — case-splitting
  simplifications for `<=` atoms between sums/concatenations sharing a
  common sub-term.
- `mk_leq_core`'s "common prefix/suffix" and "last non-zero bit" extract
  rewrites for `<=` against partially-numeral concatenations.
- `propagate_extract` — chopping high/low bits off `bvadd`/`bvmul` chains
  before re-extracting.
- `mk_mul_eq` / equation-solving helpers for products and concatenations
  (`isolate_term`, `mk_eq_concat`, `mk_eq_bv2int`), and `m_mul2concat`.
- `mk_bv_udiv`/`mk_bv_urem`/`mk_bv_sdiv`/`mk_bv_srem`/`mk_bv_smod`'s
  constant-folding and the derived `*_i` operator desugaring — the
  *definitions* (`bvudiv`/`bvurem`) are modeled in `Z3BvTheory.fst`, but the
  signed variants' own identities (e.g. `mk_bv_sdiv`'s decomposition via
  `to_int_signed`) are not yet proved.
- `mk_bv_comp`, `mk_bv_redor`, `mk_bv_redand` — modeled in `Z3BvTheory.fst`
  but no rewrite-level lemma proved yet (e.g. `redor`/`redand` of a
  numeral).
- `mk_repeat`, `mk_bv_ext_rotate_left`/`_right`, `mk_ubv2int`/`mk_sbv2int`,
  `mk_int2bv`, `mk_bit2bool`, `mk_mkbv` — not yet modeled.
- The ten overflow-detection predicates (`mk_bvsmul_no_overflow`,
  `mk_bvumul_no_overflow`, `mk_bvsmul_overflow`, `mk_bvumul_overflow`,
  `mk_bvsdiv_overflow`, `mk_bvuadd_overflow`, `mk_bvsadd_over_underflow`,
  `mk_bvusub_underflow`, `mk_bvssub_under_overflow`, `mk_bvneg_overflow`) —
  each encodes a specific arithmetic side-condition as a boolean formula;
  none proved yet.
- `mk_bv_ite`/ite-propagation (`m_ite2id`), `bv_sort_ac`'s AC-sorting of
  `bvadd`/`bvor`/`bvand`/`bvxor` argument lists, and `mk_distinct`.

## Summary

This first pass establishes a reusable, from-scratch bit-vector semantics
(`Z3BvTheory.fst`) that is built to maximize reuse of F*'s existing, already
proved `FStar.UInt` lemma library, and proves ~25 lemmas covering the core
defining identities of `bv_rewriter.cpp`'s bitwise, arithmetic, shift,
rotate, extract/concat/extend, and comparison rewrites, plus the
`is_zero_extended` signed-vs-unsigned comparison shortcut. The large
remaining surface of search-based and arithmetic-equation-solving rewrites,
overflow predicates, and the signed-division family is catalogued above for
follow-up passes.
