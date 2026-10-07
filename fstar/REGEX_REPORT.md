# Regex/AST Audit — `seq_decl_plugin.cpp`'s `get_info`/`rex::info`

## Scope

This audit formalizes the denotational semantics of Z3's regular
expression sort and the `seq_util::rex::info` static-analysis
abstraction (`src/ast/seq_decl_plugin.cpp`, `get_info`/`mk_info_rec`
and `info::star/plus/opt/complement/concat/disj/conj/diff/xor_/
orelse/loop`), and proves that the abstraction is a *sound*
over-approximation of the language each regex expression denotes.

Four theory files, built up in layers:

| File | Contents |
|---|---|
| `Z3RegexTheory.fst` | Regular languages over an abstract alphabet as predicates `seq a -> prop`: union, intersection, complement, concat, star/plus/opt/loop, reverse, and ~20 proven algebraic lemmas (associativity, De Morgan, double-complement, star-unfold, etc.) |
| `Z3AstTheory.fst` | A minimal model of Z3's AST: `sort`, `func_decl` (with an `int_params:list int` field for `re.loop`'s bounds), `expr` (`Var`/`App`/`Quantifier` with de Bruijn indices), well-sortedness, closedness, and a denotational `eval` parameterized by an abstract `interpretation` |
| `Z3RegexExprTheory.fst` | `to_lang`: connects `App` nodes built from the regex-relevant subset of `seq_op_kind` (`src/ast/seq_decl_plugin.h`) to `Z3RegexTheory`'s `lang`, dispatching on `decl_kind` exactly as `mk_info_rec` does |
| `Z3RegexInfo.fst` | `compute_info`: a formal model of `rex::info`/`get_info`, and `lemma_compute_info_sound`, the main soundness theorem |

All four files type-check and discharge all verification conditions
with **no `admit`/`assume`/axioms**:

```
C:\fstar\fstar\bin\fstar.exe --smt C:\z3-4.13.3\z3-4.13.3-x64-win\bin\z3.exe Z3RegexInfo.fst
```

### Explicitly out of scope

- **`len_abs`'s periodic length-set refinement** (`src/util/len_abs.h`,
  `period`/`residues`): `compute_info`'s `info` record only tracks
  `nullable`, `min_length`, and `max_length` (as a possibly-infinite
  `ebound`), the same `[min_length, max_length]` interval `len_abs`
  additionally refines with a residue class. This is a deliberate
  scope reduction: `len_abs` is a self-contained refinement layered on
  top of the interval formalized here, and is future work.
  `compute_info`'s bounds are sound (if less tight) with respect to
  this same interval.
- `re.of_pred`'s predicate argument is left uninterpreted (no
  executable Boolean-valued function is modeled), matching that
  `get_info` itself gives it no `min_length`/`max_length`/`nullable`
  beyond `l_undef`/unbounded.
- `OP_RE_POWER` (a parse-time alias eagerly rewritten by
  `seq_rewriter.cpp` to a fixed `OP_RE_CONCAT` chain) and
  `OP_RE_DERIVATIVE` (an internal Brzozowski-derivative helper) are
  omitted: neither contributes a new combinator beyond what
  `Z3RegexTheory.fst` already models.
- `OP_SEQ_IN_RE`/membership constraints and the general string-valued
  sequence operators (`OP_SEQ_CONCAT`, `OP_SEQ_AT`, etc.) are not
  modeled; this file is purely about expressions of *regex sort*.
- `classical` is carried through `compute_info`'s `info` record for
  structural fidelity with the C++ struct, but no property is proved
  about it.

## Result: a genuine soundness bug found in `info::diff`

While proving `lemma_sound_diff` (`seq_util::rex::info::diff`'s
nullability computation is sound with respect to `re_diff`'s actual
language `L(r) \ L(s)`), an exhaustive 9-case analysis of the 3-valued
nullable lattice (`l_true`/`l_false`/`l_undef`, crossed for `r` and
`s`) showed the real C++ formula is **unsound** at exactly one case:

```cpp
// src/ast/seq_decl_plugin.cpp, info::diff (before fix)
((nullable == l_true && rhs.nullable == l_false) ? l_true :
 ((nullable == l_false || rhs.nullable == l_false) ? l_false : l_undef))
```

At `(nullable = l_undef, rhs.nullable = l_false)` this formula returns
`l_false` (claiming `L(r) \ L(s)` is definitely *not* nullable),
solely because `rhs.nullable == l_false`. But this is unsound: a
regex `r` with unknown nullability can still denote the empty word.

**Concrete counterexample.** Let `r = (str.to_re s)` for a symbolic
sequence variable `s` with `min_length = 0` (so `r`'s own `nullable`
is correctly `l_undef`, since `s` may or may not be empty), and let
`r2 = (re.range "a" "a")` (`nullable = l_false`, since every word of
`re.range` has length exactly 1). If the solver's model happens to
assign `s := ""` (consistent with `min_length = 0`), then
`L(r) \ L(r2)` *does* contain the empty word (`"" ∈ L(r)`, `"" ∉
L(r2)`), yet `info::diff` reports `nullable = l_false` for this
difference — an unsound claim that could let a caller relying on
`rex::info` incorrectly conclude `¬(empty ∈ L(r \ r2))`.

By contrast, exhaustive case analysis of the same 9 cases for
`concat`, `disj` (union), `conj` (intersection), and `xor_` confirmed
those four operators' nullable formulas are **all fully sound** as
written; `diff` is the only one of the five binary operators with
this bug.

### The fix

`compute_info`'s `info_diff` (`Z3RegexInfo.fst`) uses the corrected
formula, proved sound (`lemma_sound_diff`):

```fstar
let n =
  if i1.nullable = LTrue && i2.nullable = LFalse then LTrue
  else if i1.nullable = LFalse then LFalse
  else LUndef
```

i.e. dropping the erroneous `rhs.nullable == l_false` disjunct from
the false-branch condition. The corresponding one-line fix has been
applied to `src/ast/seq_decl_plugin.cpp`'s `info::diff`:

```cpp
((nullable == l_true && rhs.nullable == l_false) ? l_true :
 ((nullable == l_false) ? l_false : l_undef))
```

`test-z3 /a` (all 111 unit tests, including `seq_rewriter` and
`seq_parikh`, which exercise `rex::info` extensively) passes
unchanged after this fix.

## Coverage

Every `re_op`/`seq_op_kind` case `get_info`/`mk_info_rec` handles for
regex-sorted expressions is modeled and proved sound in
`lemma_compute_info_sound`'s structural induction: `re.none`,
`re.all`, `re.allchar`, `re.of_pred`, `re.range`, `(str.to_re _)`,
`re.+`, `re.*`, `re.opt`, `re.complement`, `re.reverse`, `re.++`,
`re.union`, `re.inter` (`conj`), `re.diff`, `re.^xor` (`xor_`), and
both forms of `re.loop` (unbounded-lower-bound-only and
`{lo, hi}`-bounded).

## Addendum: `info.interpreted`/`is_ground` and PR #11091

`seq_util::rex::info` has a fifth field, `interpreted`, exposed as
`rex::is_ground(e) = get_info(e).interpreted`
(`seq_decl_plugin.h:672`), and relied on by `seq_rewriter.cpp`'s
`mk_eq_core` to gate a ground-regex bisimulation shortcut for regex
equality (`re().is_ground(l) && re().is_ground(r)` before running
`seq::regex_bisim`). The original four-file formalization above
proved soundness of `nullable`/`min_length`/`max_length` but did not
model `interpreted` at all — it could not have caught
[PR #11091](https://github.com/Z3Prover/z3/pull/11091)
("Keep symbolic regex ranges out of ground equivalence checks",
fixing [issue #11090](https://github.com/Z3Prover/z3/issues/11090)),
which fixes exactly that field: a symbolic `re.range lo hi`
(non-literal endpoints) was unconditionally reported as
`interpreted = true`, letting the ground-bisimulation shortcut
incorrectly decide an equality between a symbolic range and a
concrete one that could in fact be satisfiable (reported repro:
`lo = "b"`, `hi = "c"`, `(= (re.range lo hi) (re.range "b" "c"))`
reduced to `false` when it is actually `sat`).

This has since been added:

- `Z3RegexExprTheory.fst`'s `seq_lit` now carries a `classify : expr
  -> option (seq a)` field distinguishing literal leaves
  (`classify e = Some w`, standing in for `m.is_value`/
  `u.str.is_string`) from symbolic ones (`classify e = None`,
  denotation only available via `leaf_interp`, which may vary by
  model). `eval_leaf` dispatches through `classify` first, so a
  literal's value is, by construction, the same under any `seq_lit`
  agreeing on `classify` (`lemma_eval_leaf_ground`).
- `Z3RegexInfo.fst`'s `info` record gained an `interpreted:bool`
  field, propagated through every combinator exactly as `classical`
  already was (conjunction for binary operators, pass-through for
  unary ones), and computed at the two leaf cases that can actually
  be symbolic: `Re_range` (`is_ground_leaf sl lo && is_ground_leaf sl
  hi` -- the corrected formula) and `Re_seq_to_re`
  (`is_ground_leaf sl s`).
- `lemma_compute_info_interpreted_sound`, a second main theorem (by
  the same structural induction as `lemma_compute_info_sound`,
  reusing a small suite of new `lemma_*_cong` language-congruence
  lemmas for `Z3RegexTheory`'s combinators), proves: for any two
  `seq_lit`s agreeing on leaf classification (`compatible`),
  `compute_info`'s `interpreted` flag agrees between them, and
  whenever it is `true`, `to_lang` denotes *equivalent* languages
  under both -- i.e. `interpreted` really does certify
  model-independence.

**Direct confirmation the model catches this bug class**: reverting
`compute_info`'s `Re_range` case to the old unconditional
`interpreted = true` (instead of the corrected
`is_ground_leaf sl lo && is_ground_leaf sl hi`) was checked to make
`lemma_compute_info_interpreted_sound` **fail to verify** (F* reports
`Assertion failed` at exactly that case), confirming the
formalization is precise enough to reject the PR #11091 bug and
accept its fix.
