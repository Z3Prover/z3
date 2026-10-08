# F* Formalization of `src/ast/rewriter/seq_rewriter.cpp` — Coverage Report

See [`README.md`](README.md) for the top-level index of this F*
formal-verification audit series.

This is the self-contained report for **all** `seq_rewriter.cpp`
coverage across the project: the "sequence core" (concatenation,
length, extract, at/nth, contains, prefix/suffix, replace, reverse,
power) and the `OP_SEQ_IN_RE` (`str.in_re`) membership rewrites,
together with `src/ast/rewriter/seq_derive.cpp`'s symbolic-derivative
engine that `mk_str_in_regexp` relies on for ground-string membership,
and `src/ast/seq/seq_axioms.cpp`'s quantifier-instantiation axioms (a
distinct module: it does not rewrite terms, but asserts ground clauses
that pin down "complex" sequence operations in terms of "basic" ones
for the solver core). It supersedes and absorbs `SEQ_REPORT.md` (now
removed) and the `OP_SEQ_IN_RE`/`seq_derive.cpp` addendum that
previously lived at the end of [`REGEX_REPORT.md`](REGEX_REPORT.md)
(which remains the report for `seq_decl_plugin.cpp`'s `get_info`/
`rex::info` static-analysis abstraction, a different subject).

Four independent layers, six proof files:

| Layer | Theory file | Proof file | Subject |
|---|---|---|---|
| Sequence core | [`Z3SeqTheory.fst`](Z3SeqTheory.fst) | [`Z3SeqRewrites.fst`](Z3SeqRewrites.fst) | `mk_seq_*` functions |
| Regex membership | [`Z3RegexTheory.fst`](Z3RegexTheory.fst) (+ [`Z3RegexExprTheory.fst`](Z3RegexExprTheory.fst)) | [`Z3SeqDerive.fst`](Z3SeqDerive.fst), [`Z3RegexMembership.fst`](Z3RegexMembership.fst) | `mk_str_in_regexp` / `seq_derive.cpp`'s `derive_core` |
| Regex algebra | [`Z3RegexTheory.fst`](Z3RegexTheory.fst) | [`Z3RegexRewrites.fst`](Z3RegexRewrites.fst) | `mk_re_*` functions dispatched from `mk_app_core` |
| Axiom soundness | [`Z3SeqTheory.fst`](Z3SeqTheory.fst) (+ [`Z3SeqRewrites.fst`](Z3SeqRewrites.fst)) | [`Z3SeqAxioms.fst`](Z3SeqAxioms.fst) | `seq::axioms` (`src/ast/seq/seq_axioms.cpp`) |

Toolchain used: [F*](https://github.com/FStarLang/FStar) `v2026.09.27`
(Windows x64) with Z3 `4.13.3` as the SMT backend (F* pins an exact Z3
version; this is independent of the Z3 binary built from this
repository). All six proof files type-check and discharge all verification
conditions with **no `admit`/`assume`/axioms**:

```
C:\fstar\fstar\bin\fstar.exe --smt C:\z3-4.13.3\z3-4.13.3-x64-win\bin\z3.exe Z3SeqRewrites.fst
C:\fstar\fstar\bin\fstar.exe --smt C:\z3-4.13.3\z3-4.13.3-x64-win\bin\z3.exe Z3SeqDerive.fst
C:\fstar\fstar\bin\fstar.exe --smt C:\z3-4.13.3\z3-4.13.3-x64-win\bin\z3.exe Z3RegexMembership.fst
C:\fstar\fstar\bin\fstar.exe --smt C:\z3-4.13.3\z3-4.13.3-x64-win\bin\z3.exe Z3RegexRewrites.fst
C:\fstar\fstar\bin\fstar.exe --smt C:\z3-4.13.3\z3-4.13.3-x64-win\bin\z3.exe Z3SeqAxioms.fst
```

## Scope

**In scope**:

- The "sequence core" of `seq_rewriter.cpp` — concatenation, length,
  extract/substr, at/nth, contains, prefix/suffix, replace, reverse,
  power, unit, and the recursive-unrolling helpers
  first/rest/last/butlast.
- `mk_seq_map`/`mk_seq_mapi`/`mk_seq_foldl`/`mk_seq_foldli`
  (`seq_rewriter.cpp:2117-2199`): the empty/singleton/concat-distribute
  rewrite rules for all four higher-order sequence operators,
  modeling the Z3 Array-sort function argument `f` as an arbitrary
  F* function.
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
- `replace_all`, `replace_re`, `replace_re_all`, `last_index`.
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

## `mk_app_core` dispatch coverage

`seq_rewriter::mk_app_core` (`seq_rewriter.cpp:154-369`) is the single
entry point that dispatches every seq/regex builtin to its `mk_*`
handler. The table below lists **every** method it dispatches to, and
for each one: whether it is covered by this report, and exactly what
part of the code that coverage corresponds to.

**Sequence/string family:**

| Dispatched method | Covered? | What is verified |
|---|---|---|
| `mk_seq_unit` | partial | see Part 1 (`mk_seq_unit` row) |
| `mk_seq_concat` | yes | associativity, empty-unit identities (Part 1) |
| `mk_seq_length` | yes | concat/unit/empty/power/extract/map length laws (Part 1) |
| `mk_seq_power` | yes | non-positive/one/multiplicative-exponent cases (Part 1) |
| `mk_seq_extract` | partial | degenerate-bound and composition cases only (Part 1) |
| `mk_seq_contains` | partial | empty-needle/haystack and extract-derived cases (Part 1) |
| `mk_seq_at` | partial | out-of-bounds and in-range cases (Part 1) |
| `mk_seq_nth` / `mk_seq_nth_i` | partial | unit and extract-shift cases (Part 1) |
| `mk_seq_prefix` | partial | empty/reflexive/concat-intro cases (Part 1) |
| `mk_seq_suffix` | partial | empty/concat-intro cases (Part 1) |
| `mk_seq_index` | no | not modeled (position-search, not yet formalized) |
| `mk_seq_last_index` | no | out of scope (Part 1) |
| `mk_seq_replace` | partial | empty-pattern/trivial-equality/not-found cases (Part 1) |
| `mk_seq_replace_all` | no | out of scope (Part 1) |
| `mk_seq_map` | yes | empty/unit/concat-distribute cases (Part 1) |
| `mk_seq_mapi` | yes | empty/unit/concat-distribute + index arithmetic (Part 1) |
| `mk_seq_foldl` | yes | empty/unit/concat-distribute cases (Part 1) |
| `mk_seq_foldli` | yes | empty/unit/concat-distribute + index arithmetic (Part 1) |
| `mk_seq_replace_re` | no | out of scope |
| `mk_seq_replace_re_all` | no | out of scope |
| `mk_str_to_regexp` | yes | `lemma_in_re_to_re` (Part 2, via `mk_str_in_regexp`) |
| `mk_str_in_regexp` | partial | base cases, `to_re`/empty-string/opt/prefix/suffix rewrites, ground-string derivative chase (Part 2) |
| `mk_str_le` / `mk_str_lt` | no | not modeled (needs a lexicographic-order theory) |
| `mk_str_from_code` / `mk_str_to_code` | no | not modeled |
| `mk_str_is_digit` | no | not modeled |
| `mk_str_units` | no | not modeled |
| `mk_str_itos` / `mk_str_stoi` | no | not modeled (integer/string conversion) |
| `mk_str_ubv2s` / `mk_str_sbv2s` | no | not modeled (bit-vector/string conversion) |

**Regex family (all dispatched from `mk_app_core`, all proved in Part
3 / [`Z3RegexRewrites.fst`](Z3RegexRewrites.fst) unless noted):**

| Dispatched method | Covered? | What is verified |
|---|---|---|
| `mk_re_plus` | yes | `emp+=emp`/`all+=all`/`eps+=eps`/`a*+=a*` -- the 4 "clean algebraic" branches (nested-loop arithmetic branch not applicable here) |
| `mk_re_star` | yes | `emp*`/`all*`/`.+*`/`eps*`/`a+*=a*`/`a**=a*`/`(eps\|a)*=a*`/`(a*\|b)*=(a\|b)*`/`(a*b*)*=(a\|b)*` -- 9 of its ~11 branches; info-dependent `min_length`/subset-detection branches not covered |
| `mk_re_opt` | yes | definitional identity with `re_union(epsilon,a)`, already established in `Z3RegexTheory.fst` |
| `mk_re_reverse` | yes | push-through for concat/star/plus/union/inter/diff/xor/complement/opt/loop/double-reverse -- 12 of its ~15 branches; `ite` and literal-string-data branches not covered |
| `mk_re_union0` / `mk_re_union` | partial | idempotence, empty/full absorption, `a*\|eps=a*`, complement absorption; `try_collapse_re_union`/AC-normalization/`ite`-hoisting not covered |
| `mk_re_complement` | partial | both De Morgan directions, empty/full swap, double-complement, `~eps = Sigma-char+`; `ite`-hoisting not covered |
| `mk_re_inter0` / `mk_re_inter` | partial | idempotence, empty/full absorption, complement absorption; `try_collapse_re_inter`/AC-normalization/`ite`-hoisting not covered |
| `mk_re_diff` | yes (via citation) | `a\b = a & ~b`, exactly `lemma_diff_is_inter_compl` in `Z3RegexTheory.fst`; the `range_predicate` fast path not covered |
| `mk_re_xor0` / `mk_re_xor` | yes | self-xor/empty-identity/full-identity/complement-distribution (all 3 directions); AC-normalization not covered |
| `mk_re_loop` | partial | `lo>hi` emptiness, `loop 0 0 = eps`, `loop 1 1 = a`, `loop 0 unbounded = a*`; nested-loop combination arithmetic not covered |
| `mk_re_power` | yes (via citation) | reduces to `mk_re_loop`'s `lo=hi` case, i.e. `lemma_loop_exact` |
| `mk_re_range` | partial | inverted-range-emptiness and singleton-range identity, stated against an abstract `in_range` predicate; concrete-literal extraction and symbolic length-pruning not covered |
| `mk_re_concat` | partial | `all.all=all`, empty absorption, epsilon unit (via citation), literal concatenation, `a*.a*=a*`, `a*.a=a.a*`; `rex::info`-dependent absorption rules, loop-addition combination, and `ite`-hoisting not covered |

## Part 1: sequence core (`Z3SeqRewrites.fst`)

### Coverage by function

| `seq_rewriter.cpp` function | Lines | Lemma(s) in [`Z3SeqRewrites.fst`](Z3SeqRewrites.fst) | Gaps / not proved |
|---|---|---|---|
| `mk_seq_unit` | 420-432 | — | char->string literal coalescing (not applicable to the abstract model) |
| `mk_seq_concat` | 441-513 | `lemma_concat_assoc`, `lemma_concat_empty_r`, `lemma_concat_empty_l` | literal-coalescing / iterative-flattening implementation detail (engineering, not a new semantic law) |
| `mk_seq_reverse` | 513-543 | `lemma_reverse_unit`, `lemma_reverse_concat`, `lemma_reverse_reverse` | — |
| `mk_seq_length` | 543-607 | `lemma_len_concat`, `lemma_len_unit`, `lemma_len_empty`, `lemma_len_power`, `lemma_len_extract_nat` (general position), `lemma_len_extract_from_zero` (exact rule: `len(extract(x,0,z)) = min(z,len(x))`), `lemma_len_map` (`len(map(f,s)) = len(s)`) | length-through-`replace` (`len(y)=len(z) ==> len(replace(x,y,z))=len(x)`) -- out of scope (char-level `replace` length-preservation not modeled) |
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
| `mk_seq_map` | 2117-2137 | `lemma_map_empty`, `lemma_map_unit`, `lemma_map_concat`, `lemma_len_map`, `lemma_nth_map` | `f` is modeled as an arbitrary total F* function; this is sound since the rewrite only ever *applies* `f` (never inspects it), matching how `array.mk_select` opaquely applies the Z3 array value `f` |
| `mk_seq_mapi` | 2139-2159 | `lemma_mapi_empty`, `lemma_mapi_unit`, `lemma_mapi_concat` | same `f`-as-function abstraction as `mk_seq_map` |
| `mk_seq_foldl` | 2161-2179 | `lemma_fold_left_empty`, `lemma_fold_left_unit`, `lemma_fold_left_concat` | same `f`-as-function abstraction |
| `mk_seq_foldli` | 2181-2199 | `lemma_fold_lefti_empty`, `lemma_fold_lefti_unit`, `lemma_fold_lefti_concat` | same `f`-as-function abstraction |
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

`map`/`mapi`/`fold_left`/`fold_lefti` (`seq.map`/`seq.mapi`/
`seq.foldl`/`seq.foldli`, `OP_SEQ_MAP`/`OP_SEQ_MAPI`/`OP_SEQ_FOLDL`/
`OP_SEQ_FOLDLI`) were added in a still later pass: `Z3SeqTheory.fst`
gained four new recursively-defined combinators modeling these
operators abstractly (the Z3 Array-sort function argument `f` is
modeled as an arbitrary F* function of matching arity/order, since the
rewrite rules only ever *apply* `f` via `array.mk_select` and never
inspect it), and `Z3SeqRewrites.fst` proves each of `mk_seq_map`'s/
`mk_seq_mapi`'s/`mk_seq_foldl`'s/`mk_seq_foldli`'s three rewrite cases
(empty, singleton/`unit`, and the recursive `str.++`-distributing
case) as a lemma, plus the auxiliary `len(map(f,s)) = len(s)` and
`nth_i(map(f,s),i) = f(nth_i(s,i))` facts documented in `mk_seq_map`'s
doc comment. `mapi`/`foldli`'s indexed-concat lemmas needed to thread
the index arithmetic `i + len(s)` through the induction, matching the
`j = i + len(s1)` computation at seq_rewriter.cpp:2152/2194.

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

## Part 3: regex algebra (`Z3RegexRewrites.fst`)

[`Z3RegexRewrites.fst`](Z3RegexRewrites.fst) proves that the `mk_re_*`
rewrite rules dispatched from `mk_app_core` preserve the `lang a`
semantics defined in [`Z3RegexTheory.fst`](Z3RegexTheory.fst), i.e.
that each rewrite is a sound language-equivalence (`equiv`), not just
a syntactic transformation. Scope follows the same "breadth over
completeness" policy as Parts 1-2: every function dispatched on
regex arguments is covered for its "clean algebraic" branches
(identities, absorptions, idempotences, De Morgan laws, push-through
rules); branches that depend on `rex::info`'s `min_length`/`nullable`
static analysis, on `is_subset`/`merge_regex_sets`/`try_collapse_re_*`
syntactic-subset detection, or that are pure term-restructuring
(`ite`-hoisting, AC-normalization, concat flattening) are explicitly
listed as not covered per function below.

Two new reusable building blocks, beyond what `Z3RegexTheory.fst`
already supplied, carry most of the proof weight:

- **Pointwise monotonicity** (`lemma_pow_mono`, `lemma_star_mono`,
  `lemma_concat_mono`/`lemma_concat_congr`): lifts a per-word language
  containment/equivalence fact through `re_pow`/`re_star`/`re_concat`.
  This is the generic "closed language absorbs its own
  repetitions/unions" argument used throughout `mk_re_star` (e.g.
  `(a*|b)* == (a|b)*`) and `mk_re_reverse`.
- **`lemma_reverse_pow`** (`reverse(L^n) == (reverse L)^n`): generalizes
  `Z3RegexTheory.fst`'s existing `lemma_reverse_concat_lang` (one
  concatenation) to `n` repetitions by induction, via
  `lemma_pow_add` reassociation (since `re_pow` is left-recursive, the
  naive witness swap produces the wrong concatenation order and must
  be corrected with the already-proved pow-addition identity). This is
  the key lemma behind `mk_re_reverse`'s star/plus/loop cases.
- **`lemma_star_pow_comm`** (`L* . L^n == L^n . L*`): a general
  commutativity fact (both sides describe "n-or-more copies of L"),
  needed because `re_loop_lo` is defined `pow . star` but reversing a
  concatenation naturally produces `star . pow`.

### Coverage by function

| `seq_rewriter.cpp` function | Lines | Lemma(s) in [`Z3RegexRewrites.fst`](Z3RegexRewrites.fst) | Not covered |
|---|---|---|---|
| `mk_re_plus` | 4319-4349 | `lemma_re_plus_empty`, `lemma_re_plus_full`, `lemma_re_plus_epsilon`, `lemma_re_plus_star_idem` | — (all 4 branches covered) |
| `mk_re_star` | 4165-4242 | `lemma_re_star_full`, `lemma_re_star_allchar`, `lemma_re_star_empty`, `lemma_re_star_epsilon`, `lemma_re_star_plus_idem`, `lemma_re_star_star_idem`, `lemma_re_star_union_epsilon`, `lemma_re_star_union_star_absorb`, `lemma_re_star_concat_star_star` | the `(Sigma*.S)* = eps\|Sigma*.S` rule (associativity-heavy, deferred); `min_length`/subset-detection branches; `ite`-hoisting |
| `mk_re_opt` | 4349-end | (cites `Z3RegexTheory.fst`'s `lemma_opt_is_loop_0_1`; `re_opt` is definitionally `re_union(epsilon,l)`) | — |
| `mk_re_reverse` | 2876-2969 | `lemma_reverse_pow`, `lemma_reverse_star`, `lemma_reverse_plus`, `lemma_reverse_union`, `lemma_reverse_inter`, `lemma_reverse_diff`, `lemma_reverse_xor`, `lemma_reverse_complement`, `lemma_reverse_opt`, `lemma_reverse_loop`, `lemma_reverse_loop_lo` (+ cites `lemma_reverse_concat_lang`/`lemma_reverse_reverse_lang` from `Z3RegexTheory.fst`) | the `ite`-tree branch; the `is_full_seq`/`is_empty`/`is_range`/`is_full_char`/`is_of_pred` self-invariant branches (need `len w=1 ==> reverse w==w`, not formalized); literal-string-data branches (`to_re(reverse string)`, no string-literal type in this model) |
| `mk_re_union0` / `mk_re_union` | 3814-3872 | `lemma_union_idem`, `lemma_union_empty_l/r`, `lemma_union_full_l/r`, `lemma_union_absorb_subset`, `lemma_re_union_star_epsilon`, `lemma_union_compl_full` | `try_collapse_re_union`/`mk_regex_union_normalize` (AC-normalization, syntactic subset detection via `is_subset`/`merge_regex_sets`); `ite`-hoisting |
| `mk_re_complement` | 3880-3924 | `lemma_inter_union_compl_demorgan` (dual of `Z3RegexTheory.fst`'s `lemma_union_inter_compl_demorgan`), `lemma_compl_empty`, `lemma_compl_full`, `lemma_compl_epsilon_is_plus_allchar` (+ cites `lemma_compl_compl`) | `ite`-hoisting |
| `mk_re_inter0` / `mk_re_inter` | 3924-3981 | `lemma_inter_idem`, `lemma_inter_empty_l/r`, `lemma_inter_full_l/r`, `lemma_inter_compl_empty` | `try_collapse_re_inter`/`mk_regex_inter_normalize`; `ite`-hoisting |
| `mk_re_diff` | 3981-4010 | (cites `Z3RegexTheory.fst`'s `lemma_diff_is_inter_compl` directly -- it literally *is* `mk_re_diff`'s fallback definition) | the `range_predicate_to_regex`/`regex_to_range_predicate` fast path (needs the `mk_re_range` element-ordering model) |
| `mk_re_xor0` / `mk_re_xor` | 4010-4080 | `lemma_xor_self_empty`, `lemma_xor_empty_l/r`, `lemma_xor_full_l/r`, `lemma_xor_compl_compl`, `lemma_xor_compl_l`, `lemma_xor_compl_r` | expression-id-based AC normalization (term-ordering, no language content) |
| `mk_re_loop` | 4080-4148 | `lemma_loop_empty_inverted`, `lemma_loop_0_0`, `lemma_loop_1_1`, `lemma_loop_lo_zero_is_star` (+ cites `Z3RegexTheory.fst`'s `lemma_loop_exact`/`lemma_loop_lo_def`) | nested-loop combination (`(loop (loop a lo) lo2) = (loop a lo*lo2)` and its bounded variant -- needs a `pow`-multiplication lemma not yet written); `UINT_MAX` overflow guards (machine arithmetic, no language content) |
| `mk_re_power` | 4148-4165 | (reduces definitionally to `mk_re_loop`'s `lo=hi` case, i.e. `lemma_loop_exact`) | — |
| `mk_re_range` | 4242-4319 | `lemma_range_empty_of_unsat`, `lemma_range_singleton` (both stated against an abstract `in_range` predicate, since this model has no concrete character-order theory) | concrete-literal extraction (`zstring`/`str().is_unit`/`m_util.is_const_char`); `min_length`/`max_length` symbolic-bound emptiness pruning |
| `mk_re_concat` | 3588-3813 | `lemma_concat_full_full`, `lemma_concat_empty_lang_l/r`, `lemma_concat_to_re`, `lemma_concat_star_star_self`, `lemma_concat_star_self_comm` (+ cites `Z3RegexTheory.fst`'s `lemma_concat_unit_l/r` for the epsilon-unit branches) | the `rex::info`/`accepts_empty_word`/`starts_with_full_seq`/`ends_with_full_seq`/`all_inter_arms_end_with_full_seq` branches (need `rex::info` static analysis, not modeled here); loop-addition combination (subset direction is easy via `lemma_pow_concat_intro` generalized to ranges, converse direction needs nat-arithmetic case splitting, not yet written); `ite`-hoisting; the final concat-flattening re-association (bookkeeping, not a semantic law) |

All lemmas above compile with **zero `admit`/`assume`**; a full clean
recompile of all 24 `.fst` files in this directory (deleting every
`.checked` file first) succeeds with no errors.

## Part 4: axiom soundness (`Z3SeqAxioms.fst`)

[`Z3SeqAxioms.fst`](Z3SeqAxioms.fst) covers a different C++ module
from Parts 1-3: `src/ast/seq/seq_axioms.cpp` (the `seq::axioms`
class). This module does not rewrite terms -- it emits ground clauses
(asserted directly to the SAT/SMT core, with fresh Skolem constants
for existentials) that axiomatize "complex" string operations
(`str.extract`, `str.at`, `str.prefixof`/`str.suffixof`, ...) in terms
of "basic" ones (`str.++`, `str.len`, `str.nth_i`, equality).
Soundness of such an axiom means the clause, restated at the `seq a`
level of [`Z3SeqTheory.fst`](Z3SeqTheory.fst) with real existentials in
place of Skolem constants, is a theorem -- not an independent
assumption. This is a first installment; see "Not covered" below for
the remaining axiom-generating functions.

A new general-purpose building block introduced here: `mismatch p s`
(a computable function, not just an existence proof) returns the
first index where two sequences disagree, used to prove the
`str.prefixof`/`str.suffixof` "tightest counterexample" axioms by
explicit construction rather than classical existence reasoning.

### Coverage by function

| `seq_axioms.cpp` function | Lines | Lemma(s) in [`Z3SeqAxioms.fst`](Z3SeqAxioms.fst) | Not covered |
|---|---|---|---|
| `unit_axiom` | 1214-1218 | `lemma_unit_injective` | — |
| `at_axiom` | 606-644 | `lemma_at_decompose` (+ cites `lemma_at_oob`/`lemma_at_in_range` from `Z3SeqRewrites.fst`) | the literal-position fast path (`a.is_numeral(i,...)`, an unrolled special case of the same fact) |
| `nth_axiom` | 654-677 | `lemma_nth_axiom_sound` (restates `lemma_at_in_range`) | the ground-string literal fast path (`seq.str.is_string`) |
| `tail_axiom` / `drop_last_axiom` | 265-280 | (both reduce to `lemma_at_decompose` at `i=0` resp. `i = len s - 1`, combined with `lemma_drop_all`) | `is_tail`/`is_drop_last` pattern-matching itself (syntactic dispatch, not a soundness question) |
| `length_axiom`, `str.extract` branch | 1368-1407 | `lemma_length_axiom_extract` | the `unit`/`empty`/`concat`/`string`-literal branches (trivial rewrite-to-self, already covered by `Z3SeqRewrites.fst`'s `lemma_len_concat`/`lemma_len_unit`/`lemma_len_empty`) and the fallback `n >= 0` branch (trivial, `len` is `nat`-valued) |
| `extract_axiom`, general case | 196-261 | `lemma_extract_axiom_general` (all 5 length/reconstruction clauses) | — |
| `extract_prefix_axiom` / `extract_suffix_axiom` | 338-369 | (special cases of `lemma_extract_axiom_general` at `i=0` resp. `l = len s - i`; not yet restated as standalone corollaries) | — |
| `prefix_axiom` | 1321-1356 | `lemma_prefix_mismatch` (+ helper `mismatch`/`lemma_mismatch_correct`) | the `len s > len t` guard side (trivially discharges the clause, no content); the single-character (`max_length <= 1`) fast path in `tightest_prefix` |
| `suffix_axiom` | 1286-1319 | `lemma_suffix_mismatch` (derived from `lemma_prefix_mismatch` via `reverse`) | same as `prefix_axiom` |
| `indexof_axiom` / `last_indexof_axiom` | 431-577 | not covered | the full `indexof`/`last_indexof` semantics (smallest/largest valid occurrence position) -- needs a `index_of` model function in `Z3SeqTheory.fst`, not yet added |
| `replace_axiom` / `replace_all_axiom` | 578-605, 1144-1199 | not covered | `replace`/`replace_all` already have `lang`-level definitions and partial lemmas in `Z3SeqRewrites.fst` (`lemma_replace_empty_pat`, `lemma_replace_eq`, `lemma_replace_not_contains`), but the axiom-clause form (Skolem decomposition) is not yet restated |
| `replace_re_axiom` / `replace_re_all_axiom` | 1122-1213 | not covered | needs `seq_derive.cpp`-style regex-membership bridging, not yet done for this module |
| `itos_axiom` / `stoi_axiom` / `stoi_axiom_re` | 678-829 | not covered | needs a `string <-> int` conversion model (digit decomposition), not yet built |
| `ubv2s_axiom` / `ubv2s_len_axiom` / `ubv2ch_axiom` | 830-963 | not covered | needs a bit-vector-to-string model, not yet built |
| `is_digit_axiom` / `str_to_code_axiom` / `str_from_code_axiom` / `lt_axiom` / `le_axiom` | 978-1121 | not covered | needs a character-order/digit theory, not yet built (see `mk_re_range`'s abstract `in_range` predicate in `Z3RegexRewrites.fst` for a possible starting point) |
| `power_axiom` / `power_unfold_axiom` | 1232-1277 | not covered | `power` already has full `lang`-level lemmas in `Z3SeqRewrites.fst` (`lemma_len_power`, `lemma_power_nat_add`, etc.); the axiom-clause form is not yet restated |
| `unroll_not_contains` | 1409-1426 | not covered | an inductive "no occurrence at any offset" unrolling scheme; should follow directly from `contains`'s recursive definition, not yet done |
| `length_limit` | 1427-end | not covered | a simple length-upper-bound clause; trivial but not yet restated |

All lemmas above compile with **zero `admit`/`assume`**.

## Summary

All eight proof/theory files for the sequence/regex subsystem
(`Z3SeqTheory.fst`, `Z3SeqRewrites.fst`, `Z3SeqDerive.fst`,
`Z3RegexMembership.fst`, `Z3RegexTheory.fst`, `Z3RegexExprTheory.fst`,
`Z3RegexRewrites.fst`, `Z3SeqAxioms.fst`) compile cleanly from a fresh
`.checked` state with zero admits. Together they cover the full "pure
sequence" half of `seq_rewriter.cpp`, a representative slice of its
one regex/sequence bridge function (`mk_str_in_regexp`), the "clean
algebraic" core of every `mk_re_*` regex-algebra function dispatched
from `mk_app_core`, and a first installment of `seq_axioms.cpp`'s
quantifier-instantiation axioms (the positional-access core: `str.at`,
`str.nth_i`, `str.extract` and its tail/drop_last specializations,
`str.unit` injectivity, and the `str.prefixof`/`str.suffixof` tightest-
counterexample axioms). The largest remaining open areas are: (1) the
concat-boundary decomposition logic throughout the sequence core
(`mk_seq_at`/`contains`/`prefix`/`suffix`/`extract`'s `str.++`-tree
walks), (2) the `rex::info`/`is_subset`/`try_collapse_re_*` syntactic
and static-analysis machinery that backs the more aggressive `mk_re_*`
simplifications, (3) nested-loop/range arithmetic combination rules
(`mk_re_loop`'s and `mk_re_concat`'s loop-addition branches), and (4)
`seq_axioms.cpp`'s string/integer conversion, bit-vector, and
character-order axioms (`str.to_int`/`int.to_str`, `ubv2s`/`ubv2ch`,
`is_digit`/`str.to_code`/`<`/`<=`), none of which yet have a model in
this project, plus its `str.indexof`/`str.replace[_all]` axioms, which
need new `index_of`/richer `replace`-decomposition lemmas beyond what
`Z3SeqRewrites.fst` already provides.
