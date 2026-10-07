# F* Formalization of `src/ast/rewriter/seq_rewriter.cpp` — Coverage Report

See [`REPORT.md`](REPORT.md) for the top-level index of this F*
formal-verification audit series.

This is the self-contained report for **all** `seq_rewriter.cpp`
coverage across the project: the "sequence core" (concatenation,
length, extract, at/nth, contains, prefix/suffix, replace, reverse,
power) and the `OP_SEQ_IN_RE` (`str.in_re`) membership rewrites,
together with `src/ast/rewriter/seq_derive.cpp`'s symbolic-derivative
engine that `mk_str_in_regexp` relies on for ground-string membership.
It supersedes and absorbs `SEQ_REPORT.md` (now
removed) and the `OP_SEQ_IN_RE`/`seq_derive.cpp` addendum that
previously lived at the end of [`REGEX_REPORT.md`](REGEX_REPORT.md)
(which remains the report for `seq_decl_plugin.cpp`'s `get_info`/
`rex::info` static-analysis abstraction, a different subject).

Four theory/proof files, two independent layers:

| Layer | Theory file | Proof file | Subject |
|---|---|---|---|
| Sequence core | [`Z3SeqTheory.fst`](Z3SeqTheory.fst) | [`Z3SeqRewrites.fst`](Z3SeqRewrites.fst) | `mk_seq_*` functions |
| Regex membership | [`Z3RegexTheory.fst`](Z3RegexTheory.fst) (+ [`Z3RegexExprTheory.fst`](Z3RegexExprTheory.fst)) | [`Z3SeqDerive.fst`](Z3SeqDerive.fst), [`Z3RegexMembership.fst`](Z3RegexMembership.fst) | `mk_str_in_regexp` / `seq_derive.cpp`'s `derive_core` |

Toolchain used: [F*](https://github.com/FStarLang/FStar) `v2026.09.27`
(Windows x64) with Z3 `4.13.3` as the SMT backend (F* pins an exact Z3
version; this is independent of the Z3 binary built from this
repository). All four files type-check and discharge all verification
conditions with **no `admit`/`assume`/axioms**:

```
C:\fstar\fstar\bin\fstar.exe --smt C:\z3-4.13.3\z3-4.13.3-x64-win\bin\z3.exe Z3SeqRewrites.fst
C:\fstar\fstar\bin\fstar.exe --smt C:\z3-4.13.3\z3-4.13.3-x64-win\bin\z3.exe Z3SeqDerive.fst
C:\fstar\fstar\bin\fstar.exe --smt C:\z3-4.13.3\z3-4.13.3-x64-win\bin\z3.exe Z3RegexMembership.fst
```

## Scope

**In scope**:

- The "sequence core" of `seq_rewriter.cpp` — concatenation, length,
  extract/substr, at/nth, contains, prefix/suffix, replace, reverse,
  power, unit, and the recursive-unrolling helpers
  first/rest/last/butlast.
- `OP_SEQ_IN_RE` (`mk_str_in_regexp`, `seq_rewriter.cpp:3396-3527`):
  the base-language cases, the `str.to_re`/empty-string/opt/
  prefix-suffix algebraic rewrites, and the ground-string
  membership-via-derivative-chase theorem.
- `seq_derive.cpp`'s `derive_core`: the mathematical content of the
  recursive Brzozowski-derivative equations (one per regex
  combinator), as the semantic justification for the ground-string
  case of `mk_str_in_regexp` above.

**Out of scope** (not modeled, not proved):

- Sequences are modeled as F* lists over an abstract `eqtype` element
  (no separate character/string distinction), so char-level coalescing
  (`seq.unit` -> string constant) is not modeled anywhere in this report.
- `replace_all`, `replace_re`, `replace_re_all`, `last_index`, and
  `map`/`mapi`.
- The concat-boundary decomposition logic inside `mk_seq_at`,
  `mk_seq_contains`, `mk_seq_prefix`, `mk_seq_suffix`, and
  `mk_seq_extract` (walking a `str.++` tree element-by-element).
- `seq_derive.cpp`'s ITE-tree hoisting / path-pruning / cofactor
  enumeration / memoization machinery (a performance/representation
  layer, not itself a soundness obligation).
- The remainder of `mk_str_in_regexp` (symbolic-bound `re.range`,
  `replace_all`-based rewrite, `can_be_member` length pruning) and all
  other `mk_re_*` regex-algebra simplifications beyond `mk_str_in_regexp`
  itself.

## Part 1: sequence core (`Z3SeqRewrites.fst`)

### Coverage by function

| `seq_rewriter.cpp` function | Lines | Lemma(s) in [`Z3SeqRewrites.fst`](Z3SeqRewrites.fst) | Gaps / not proved |
|---|---|---|---|
| `mk_seq_unit` | 420-432 | — | char->string literal coalescing (not applicable to the abstract model) |
| `mk_seq_concat` | 441-513 | `lemma_concat_assoc`, `lemma_concat_empty_r`, `lemma_concat_empty_l` | literal-coalescing / iterative-flattening implementation detail (engineering, not a new semantic law) |
| `mk_seq_reverse` | 513-543 | `lemma_reverse_unit`, `lemma_reverse_concat`, `lemma_reverse_reverse` | — |
| `mk_seq_length` | 543-607 | `lemma_len_concat`, `lemma_len_unit`, `lemma_len_empty`, `lemma_len_power`, `lemma_len_extract_nat` (general position), `lemma_len_extract_from_zero` (exact rule: `len(extract(x,0,z)) = min(z,len(x))`) | length-through-`replace` (`len(y)=len(z) ==> len(replace(x,y,z))=len(x)`) and length-through-`map`/`mapi` -- out of scope (`map`/`mapi`/char-level `replace` length-preservation not modeled) |
| `mk_seq_power` | 607-653 | `lemma_power_nonpos`, `lemma_power_one`, `lemma_power_mul` (+ `lemma_power_nat_add` helper) | concrete numeral expansion / bounded unrolling (engineering) |
| `mk_seq_first` | 653-680 | `lemma_first_of_extract` | — |
| `mk_seq_rest` | 681-699 | `lemma_rest_of_extract` (a corollary of extract composition) | — |
| `mk_seq_last` | 700-721 | `lemma_last_of_extract` | — |
| `mk_seq_butlast` | 722-736 | `lemma_butlast_of_extract` (for completeness; the code does not special-case this) | — |
| `mk_seq_extract` | 938-1140 | `lemma_extract_neg_or_nonpos_len`, `lemma_extract_pos_ge_len`, `lemma_extract_full`, `lemma_extract_len1_is_at`, `lemma_extract_compose` (+ take/drop algebra helpers) | the concat-boundary decomposition cases (splitting an extract across a `str.++` tree) |
| `mk_seq_at` | 1351-1424 | `lemma_at_oob`, `lemma_at_in_range` | the `at`-over-`at`/`at`-over-`extract` simplification chains and the concat-boundary walk (1370-1417) |
| `mk_seq_nth` / `mk_seq_nth_i` | 1424-1540 | `lemma_nth_unit`, `lemma_nth_extract_nat` (matches the explicit code comment "`nth(s[k,\|s\|-k], b) = ... b+k<\|s\| -> nth(s,b+k)`") | the concat-walk / `ite`-flattening cases in `mk_seq_nth_i`'s main loop (1497-1532) |
| `mk_seq_contains` | 1206-1313 | `lemma_contains_empty_needle`, `lemma_contains_empty_haystack`, `lemma_contains_extract` | the syntactic/heuristic cases: literal containment, `cannot_contain_prefix/suffix` pruning, unit-by-unit case split, `reduce_by_char` |
| `mk_seq_prefix` | 2254-2389 | `lemma_prefix_empty`, `lemma_prefix_of_empty`, `lemma_prefix_reflexive`, `lemma_prefix_concat_intro` | the recursive literal-splitting algorithm (bulk of the function) |
| `mk_seq_suffix` | 2389-2466 | `lemma_suffix_empty`, `lemma_suffix_concat_intro` | same kind of literal-splitting detail, dualized |
| `mk_seq_replace` | 1813-1928 | `lemma_replace_empty_pat`, `lemma_replace_eq`, `lemma_replace_not_contains` | the "found occurrence -> splice" step is captured definitionally, not as a separately derived lemma |
| `mk_seq_last_index`, `mk_seq_replace_all`, `mk_seq_replace_re`, `mk_seq_replace_re_all` | 1540-1813, 1928-2250 | — | out of scope (iterative/regex) |
| all `mk_re_*` except `mk_str_in_regexp` | ~half the file | — | out of scope except as covered by Part 2 below |

### History

`lemma_len_extract_nat`/`lemma_len_extract_from_zero`,
`lemma_nth_extract_nat`/`lemma_nth_unit`, and
`lemma_first_of_extract`/`lemma_rest_of_extract`/`lemma_last_of_extract`/
`lemma_butlast_of_extract` were added in a later pass closing gaps
identified in an earlier version of this audit; `rest`/`butlast`
reduced directly to the pre-existing `lemma_extract_compose`, while
`first`/`last` needed the new `lemma_nth_extract_nat`/
`lemma_len_extract_nat` facts plus an auxiliary non-emptiness lemma
`lemma_extract_nat_nonempty`.

### Remaining gaps (hardest, left for future work)

The concat-boundary decomposition logic inside `mk_seq_at`,
`mk_seq_contains`, `mk_seq_prefix`, `mk_seq_suffix`, and `mk_seq_extract`
(the case splits that walk a `str.++` tree element-by-element to
figure out which operand an index/extract/containment falls into) is
the largest remaining gap in the sequence core. It is also the
highest-value target for future work, since it is the most intricate,
most frequently exercised code in the file and therefore the most
likely place for a rewrite bug to hide. Formalizing it would require
modeling sequences as lists of *segments* (rather than flat lists) to
mirror the `get_concat_units` decomposition the C++ code operates on.

## Part 2: `OP_SEQ_IN_RE` membership and symbolic derivatives

[`Z3SeqDerive.fst`](Z3SeqDerive.fst) and
[`Z3RegexMembership.fst`](Z3RegexMembership.fst) formalize
`str.in_re`/`OP_SEQ_IN_RE` (`seq_decl_plugin.h:56`) and the
mathematical content of `src/ast/rewriter/seq_derive.cpp`'s symbolic
(Brzozowski) derivative engine, working at the
[`Z3RegexTheory.fst`](Z3RegexTheory.fst) `lang a` level that
[`Z3RegexExprTheory.fst`](Z3RegexExprTheory.fst)'s `to_lang` already
denotes regex *expressions* into (`Z3RegexExprTheory.fst`'s own header
explicitly scoped `str.in_re` out as "left for a higher-level theory
of asserts" -- this is that higher-level theory).

### `Z3SeqDerive.fst`: the derivative engine

`deriv c l` is *defined* as the residual language
`{ w | c::w in L(l) }` (not an operational/syntactic construction),
and `is_nullable l` as `mem empty l`. One lemma per `derive_core` case
certifies the engine's recursive equations are exactly the true
residual-language identities:

| `seq_derive.cpp` case | Lines | Lemma(s) |
|---|---|---|
| `empty`/`epsilon` | 176-178 | `lemma_deriv_empty`, `lemma_deriv_epsilon` |
| `Sigma*`/`.` (full-seq/full-char) | 181-186 | `lemma_deriv_full`, `lemma_deriv_allchar` |
| `str.to_re s` | 189-190 | `lemma_deriv_to_re` |
| `re.of_pred`/`re.range` | 197-198 | `lemma_deriv_of_pred` (covers `re.range` too, since it is a `re_of_pred` instance) |
| `r1 \| r2`, `r1 xor r2`, `r1 & r2` | 228-247 | `lemma_deriv_union`, `lemma_deriv_xor`, `lemma_deriv_inter` |
| `~r1` | 262-266 | `lemma_deriv_complement` |
| `r1 . r2` | 201-224 | `lemma_deriv_concat`, stated as a single pointwise iff using a new `guarded` combinator (`guarded p l = fun w -> p /\ mem w l`) that uniformly covers `derive_core`'s three-way split on whether `is_nullable(r1)` is concretely true, concretely false, or a symbolic `ite` guard |
| `r1*` (star) | 268-273 | `lemma_deriv_star`, proved by a dedicated structural induction `lemma_deriv_pow_star` over the repetition count (`re_star`'s own `exists n` definition is not *definitionally* a concatenation the way `re_concat` is, so a single `elim_concat` unfold does not suffice) |
| `r1+` (plus) | 275-280 | `lemma_deriv_plus`, reduces to the star formula: expanding `r1+ == r1 . r1*` via `lemma_deriv_concat` produces an extra `is_nullable`-guarded disjunct that `lemma_deriv_star` shows is already subsumed by the first one |
| `r1?` (opt) | 282-284 | `lemma_deriv_opt` |
| `r1 \ r2` (diff) | 318-324 | `lemma_deriv_diff` |

`lemma_derivs_correct` is the ground-string correctness theorem --
`mem w l <==> is_nullable (derivs w l)` -- justifying
`mk_str_in_regexp`'s "Just check membership" loop
(`seq_rewriter.cpp:3443-3463`, `r := mk_derivative(ch, r)` then consult
`get_info(r).nullable`).

### `Z3RegexMembership.fst`: `mk_str_in_regexp` rewrite rules

Names `str.in_re`'s own denotation `in_re w l = mem w l`, then
certifies, at the `lang a` level `to_lang` already maps each regex
shape to:

| `mk_str_in_regexp` rule | Lines | Lemma |
|---|---|---|
| `(str.in_re e re.none)` -> `false` | 3401-3404 | `lemma_in_re_empty` |
| `(str.in_re e re.all)` -> `true` | 3405-3408 | `lemma_in_re_full` |
| `(str.in_re a (str.to_re s))` -> `(= a s)` | 3480-3483, 3547-3556 | `lemma_in_re_to_re` |
| `(str.in_re "" b)` -> `nullable(b)` | 3514-3519 | `lemma_in_re_empty_string` |
| ground-string derivative chase | 3443-3463 | `lemma_in_re_ground` (restates `Z3SeqDerive.lemma_derivs_correct`) |
| `b1?` / `eps\|b1` / `b1\|eps` -> `ite(len(a)=0, true, in_re(a,b1))` | 3505-3512 | `lemma_in_re_opt` (via bridging lemma `lemma_len_zero_iff_empty`: `str.len a = 0 <=> a = ""`) |
| `(str.to_re e) ++ re.all` -> `str.prefixof e a` | 3486-3489 | `lemma_in_re_prefix` (reuses `Z3SeqRewrites.fst`'s `lemma_prefix_concat_intro`/`lemma_prefix_extract_reconstruct`) |
| `re.all ++ (str.to_re e)` -> `str.suffixof e a` | 3490-3493 | `lemma_in_re_suffix` (reuses `Z3SeqRewrites.fst`'s `lemma_suffix_concat_intro`, plus a reverse/concat round-trip) |

### Not covered

- The ITE-tree hoisting, path/interval pruning, cofactor/minterm
  enumeration, and memoization machinery that is the actual bulk of
  `seq_derive.cpp`'s code (`apply_ite`/`hoist_ite`/`get_cofactors*`/the
  `m_*cache` fields): a performance/representation layer over the
  mathematically-sound recursive equations above, not itself a
  soundness obligation.
- `re.loop`'s derivative (`seq_derive.cpp:286-316`, both the
  parameterized and legacy arg-based forms), `re.reverse`'s
  (`seq_derive.cpp:333-337`, normalize-then-derive), and `ite(c,r1,r2)`'s
  (`seq_derive.cpp:324-328`, straightforward but not yet restated here).
- `mk_str_in_regexp`'s remaining rewrites: the symbolic-bound
  `re.range` reformulation into `str.len`/`str.<=` constraints
  (`seq_rewriter.cpp:3410-3441`, needs a lexicographic-order theory),
  the `str.replace_all` character-substitution rewrite
  (`seq_rewriter.cpp:3466-3476`), and the `can_be_member`-based
  length-pruning fast path (`seq_rewriter.cpp:3521-3524`, a natural
  future bridge to [`Z3LenAbsTheory.fst`](Z3LenAbsTheory.fst)/[`Z3RegexBounds.fst`](Z3RegexBounds.fst)'s
  `min_length`/`max_length` machinery, not yet wired up).
- `seq_rewriter.cpp`'s broader regex-algebra simplifications beyond
  `mk_str_in_regexp` (e.g. `mk_re_concat`'s ACI/dot-star-absorption
  rewrites) remain covered only to the extent
  [`Z3RegexTheory.fst`](Z3RegexTheory.fst)'s pre-existing `equiv`
  lemmas (`lemma_star_unfold`, `lemma_plus_is_concat_star`, etc.)
  already certify the underlying language identities.

## Summary

All four files (`Z3SeqTheory.fst`, `Z3SeqRewrites.fst`,
`Z3SeqDerive.fst`, `Z3RegexMembership.fst`) compile cleanly from a
fresh `.checked` state with zero admits. Together they cover roughly
the full "pure sequence" half of `seq_rewriter.cpp` plus a
representative slice of its one regex/sequence bridge function
(`mk_str_in_regexp`); the regex-algebra half of the file (`mk_re_*`)
and the concat-boundary decomposition logic throughout the sequence
core remain the two largest open areas.
