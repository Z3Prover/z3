# F* Formalization of Z3's Sequence Rewriter — Coverage Report

See [`REPORT.md`](REPORT.md) for the top-level index of this F*
formal-verification audit series.

This report accompanies [`Z3SeqTheory.fst`](Z3SeqTheory.fst) (axiomatization) and
[`Z3SeqRewrites.fst`](Z3SeqRewrites.fst) (proofs), which formalize and mechanically verify
a subset of the rewrite rules implemented in
`src/ast/rewriter/seq_rewriter.cpp`.

Toolchain used: [F*](https://github.com/FStarLang/FStar) `v2026.09.27`
(Windows x64) with Z3 `4.13.3` as the SMT backend (F* pins an exact Z3
version; this is independent of the Z3 binary built from this
repository). Both files type-check and discharge all verification
conditions:

```
C:\fstar\fstar\bin\fstar.exe --smt C:\z3-4.13.3\z3-4.13.3-x64-win\bin\z3.exe Z3SeqTheory.fst
C:\fstar\fstar\bin\fstar.exe --smt C:\z3-4.13.3\z3-4.13.3-x64-win\bin\z3.exe Z3SeqRewrites.fst
```

## Scope

**In scope**: the "sequence core" of `seq_rewriter.cpp` — concatenation,
length, extract/substr, at/nth, contains, prefix/suffix, replace,
reverse, power, unit, and the recursive-unrolling helpers
first/rest/last/butlast.

**Out of scope** (not modeled, not proved): the regex/automata theory
(`mk_re_*`, roughly half the file — union, intersection, complement,
Brzozowski derivatives, etc.), `replace_all`, `replace_re`,
`replace_re_all`, `last_index`, and `map`/`mapi`. Sequences are modeled
as F* lists over an abstract `eqtype` element (no separate
character/string distinction), so char-level coalescing
(`seq.unit` → string constant) is likewise not modeled.

## Coverage by function

| `seq_rewriter.cpp` function | Lines | Lemma(s) in [`Z3SeqRewrites.fst`](Z3SeqRewrites.fst) | Gaps / not proved |
|---|---|---|---|
| `mk_seq_unit` | 420-432 | — | char→string literal coalescing (not applicable to the abstract model) |
| `mk_seq_concat` | 441-513 | `lemma_concat_assoc`, `lemma_concat_empty_r`, `lemma_concat_empty_l` | literal-coalescing / iterative-flattening implementation detail (engineering, not a new semantic law) |
| `mk_seq_reverse` | 513-543 | `lemma_reverse_unit`, `lemma_reverse_concat`, `lemma_reverse_reverse` | — |
| `mk_seq_length` | 543-607 | `lemma_len_concat`, `lemma_len_unit`, `lemma_len_empty`, `lemma_len_power`, **`lemma_len_extract_nat`** (general position), **`lemma_len_extract_from_zero`** (exact rule: `len(extract(x,0,z)) = min(z,len(x))`) | length-through-`replace` (`len(y)=len(z) ⟹ len(replace(x,y,z))=len(x)`) and length-through-`map`/`mapi` — out of scope (`map`/`mapi`/char-level `replace` length-preservation not modeled) |
| `mk_seq_power` | 607-653 | `lemma_power_nonpos`, `lemma_power_one`, `lemma_power_mul` (+ `lemma_power_nat_add` helper) | concrete numeral expansion / bounded unrolling (engineering) |
| **`mk_seq_first`** | 653-680 | **`lemma_first_of_extract`** (new) | — |
| **`mk_seq_rest`** | 681-699 | **`lemma_rest_of_extract`** (new, a corollary of extract composition) | — |
| **`mk_seq_last`** | 700-721 | **`lemma_last_of_extract`** (new) | — |
| **`mk_seq_butlast`** | 722-736 | **`lemma_butlast_of_extract`** (new, for completeness; the code does not special-case this) | — |
| `mk_seq_extract` | 938-1140 | `lemma_extract_neg_or_nonpos_len`, `lemma_extract_pos_ge_len`, `lemma_extract_full`, `lemma_extract_len1_is_at`, `lemma_extract_compose` (+ take/drop algebra helpers) | the concat-boundary decomposition cases (splitting an extract across a `str.++` tree) |
| `mk_seq_at` | 1351-1424 | `lemma_at_oob`, `lemma_at_in_range` | the `at`-over-`at`/`at`-over-`extract` simplification chains and the concat-boundary walk (1370-1417) |
| **`mk_seq_nth` / `mk_seq_nth_i`** | 1424-1540 | **`lemma_nth_unit`**, **`lemma_nth_extract_nat`** (new — matches the explicit code comment "`nth(s[k,\|s\|-k], b) = ... b+k<\|s\| → nth(s,b+k)`") | the concat-walk / `ite`-flattening cases in `mk_seq_nth_i`'s main loop (1497-1532) |
| `mk_seq_contains` | 1206-1313 | `lemma_contains_empty_needle`, `lemma_contains_empty_haystack`, `lemma_contains_extract` | the syntactic/heuristic cases: literal containment, `cannot_contain_prefix/suffix` pruning, unit-by-unit case split, `reduce_by_char` |
| `mk_seq_prefix` | 2254-2389 | `lemma_prefix_empty`, `lemma_prefix_of_empty`, `lemma_prefix_reflexive`, `lemma_prefix_concat_intro` | the recursive literal-splitting algorithm (bulk of the function) |
| `mk_seq_suffix` | 2389-2466 | `lemma_suffix_empty`, `lemma_suffix_concat_intro` | same kind of literal-splitting detail, dualized |
| `mk_seq_replace` | 1813-1928 | `lemma_replace_empty_pat`, `lemma_replace_eq`, `lemma_replace_not_contains` | the "found occurrence → splice" step is captured definitionally, not as a separately derived lemma |
| `mk_seq_last_index`, `mk_seq_replace_all`, `mk_seq_replace_re`, `mk_seq_replace_re_all` | 1540-1813, 1928-2250 | — | out of scope (iterative/regex) |
| all `mk_re_*` (regex/derivative engine) | ~half the file | — | explicitly out of scope |

Bold rows mark the gaps closed in this update.

## What was added in this update

Starting from the previously-identified "easy gaps", the following
were added to [`Z3SeqRewrites.fst`](Z3SeqRewrites.fst) and proved:

1. **`lemma_len_extract_nat`** / **`lemma_len_extract_from_zero`** —
   the general law `len(extract(s,pos,ln)) = min(ln, len(s) - pos)`,
   and its `pos = 0` specialization matching the exact code comment
   `len(extract(x, 0, z)) = min(z, len(x))` in `mk_seq_length`.

2. **`lemma_nth_extract_nat`** — the general "element access commutes
   with extract" law `nth(extract(s,pos,ln), i) = nth(s, pos+i)` for
   `i < ln` and `pos+i < len(s)`. This is the semantic content behind
   the explicit case-1 rule documented in `mk_seq_nth`
   (`nth(s[k,|s|-k], b) = nth(s, b+k)` when `b+k < |s|`), and is also
   the key fact used by `first`/`rest`/`last` below. Also added
   **`lemma_nth_unit`** (`nth(unit x, 0) = x`), matching the base case
   used by both `mk_seq_nth` and `mk_seq_nth_i`.

3. **`lemma_first_of_extract`**, **`lemma_rest_of_extract`**,
   **`lemma_last_of_extract`**, **`lemma_butlast_of_extract`** — the
   four `mk_seq_first/rest/last/butlast` reductions, which were
   previously entirely unformalized. `rest` and `butlast` turned out
   to be direct corollaries of the already-proved
   `lemma_extract_compose`; `first` and `last` were proved from the
   new `lemma_nth_extract_nat`/`lemma_len_extract_nat` facts plus an
   auxiliary non-emptiness lemma `lemma_extract_nat_nonempty`.

All additions were verified end-to-end with the F*/Z3 toolchain above
(no `admit`/`assume`/axioms were introduced).

## Remaining gaps (not addressed — harder, left for future work)

The concat-boundary decomposition logic inside `mk_seq_at`,
`mk_seq_contains`, `mk_seq_prefix`, `mk_seq_suffix`, and `mk_seq_extract`
(the case splits that walk a `str.++` tree element-by-element to
figure out which operand an index/extract/containment falls into) is
the largest remaining gap. It is also the highest-value target for
future work, since it is the most intricate, most frequently exercised
code in the file and therefore the most likely place for a rewrite bug
to hide. Formalizing it would require modeling sequences as lists of
*segments* (rather than flat lists) to mirror the `get_concat_units`
decomposition the C++ code operates on.
