# Regex/AST Audit — `seq_decl_plugin.cpp`'s `get_info`/`rex::info`

## Scope

This audit formalizes the denotational semantics of Z3's regular
expression sort and the `seq_util::rex::info` static-analysis
abstraction (`src/ast/seq_decl_plugin.cpp`, `get_info`/`mk_info_rec`
and `info::star/plus/opt/complement/concat/disj/conj/diff/xor_/
orelse/loop`), and proves that the abstraction is a *sound*
over-approximation of the language each regex expression denotes.

Six theory files, built up in layers:

| File | Contents |
|---|---|
| [`Z3RegexTheory.fst`](Z3RegexTheory.fst) | Regular languages over an abstract alphabet as predicates `seq a -> prop`: union, intersection, complement, concat, star/plus/opt/loop, reverse, and ~20 proven algebraic lemmas (associativity, De Morgan, double-complement, star-unfold, etc.) |
| [`Z3AstTheory.fst`](Z3AstTheory.fst) | A minimal model of Z3's AST: `sort`, `func_decl` (with an `int_params:list int` field for `re.loop`'s bounds), `expr` (`Var`/`App`/`Quantifier` with de Bruijn indices), well-sortedness, closedness, and a denotational `eval` parameterized by an abstract `interpretation` |
| [`Z3BasicExprTheory.fst`](Z3BasicExprTheory.fst) | Recognizers and a denotational `eval_bool` for the `basic_family_id` propositional connectives, equality/distinctness, and `ite` (`src/ast/ast.h`, `enum basic_op_kind`) |
| [`Z3RegexExprTheory.fst`](Z3RegexExprTheory.fst) | `to_lang`: connects `App` nodes built from the regex-relevant subset of `seq_op_kind` (`src/ast/seq_decl_plugin.h`) to `Z3RegexTheory`'s `lang`, dispatching on `decl_kind` exactly as `mk_info_rec` does, plus a regex-sorted `ite` case built on `Z3BasicExprTheory` |
| [`Z3RegexInfo.fst`](Z3RegexInfo.fst) | `compute_info`: a formal model of `rex::info`/`get_info`, and `lemma_compute_info_sound`/`lemma_compute_info_interpreted_sound`, the main soundness theorems |
| [`Z3LenAbsTheory.fst`](Z3LenAbsTheory.fst) | `len_abs`: a formalization of `src/util/len_abs.h`/`.cpp`'s ultimately-periodic length-set abstraction, and soundness proofs for `unite`/`meet`/`opt`/`concat`/`star`/`plus`/`loop` against `Z3RegexTheory`'s `lang` |

All six files type-check and discharge all verification conditions
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
  [`Z3RegexTheory.fst`](Z3RegexTheory.fst) already models.
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

`compute_info`'s `info_diff` ([`Z3RegexInfo.fst`](Z3RegexInfo.fst)) uses the corrected
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

- [`Z3RegexExprTheory.fst`](Z3RegexExprTheory.fst)'s `seq_lit` now carries a `classify : expr
  -> option (seq a)` field distinguishing literal leaves
  (`classify e = Some w`, standing in for `m.is_value`/
  `u.str.is_string`) from symbolic ones (`classify e = None`,
  denotation only available via `leaf_interp`, which may vary by
  model). `eval_leaf` dispatches through `classify` first, so a
  literal's value is, by construction, the same under any `seq_lit`
  agreeing on `classify` (`lemma_eval_leaf_ground`).
- [`Z3RegexInfo.fst`](Z3RegexInfo.fst)'s `info` record gained an `interpreted:bool`
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

## Addendum: `ite` (`info::orelse`) and [`Z3BasicExprTheory.fst`](Z3BasicExprTheory.fst)

`mk_info_rec`'s main dispatch is a `switch` on
`to_app(e)->get_decl_kind()` guarded by `e->get_family_id() ==
u.get_family_id()` (the sequence/regex family); when `e` is *not* in
that family, the one case it still recognizes is `u.m.is_ite(e, c, t,
f)` -- a regex-sorted `(ite c t f)`, answered with `i1.orelse(i2)`
where `i1 = get_info_rec(t)`, `i2 = get_info_rec(f)`. Since `is_ite`
is a generic AST-level recognizer from the *basic* family
(`src/ast/ast.h`, `basic_family_id`/`enum basic_op_kind`), modeling
this case needed a new, independent theory of that family:

- **[`Z3BasicExprTheory.fst`](Z3BasicExprTheory.fst)** (new file): recognizers (`is_basic_op`,
  `decl_kind_of`, mirroring `OP_TRUE`..`OP_IMPLIES`'s declaration
  order exactly, index 0-9) and a denotational evaluator `eval_bool`
  for the propositional connectives (`and`/`or`/`not`/`implies`/
  `xor`, `and`/`or` modeled as the genuinely n-ary operators Z3 builds
  them as), equality/distinctness (`=`/`distinct`, comparing the
  generic `Z3AstTheory.eval` denotation of arguments of any sort, via
  `value:eqtype`), truth constants, and `ite` (for genuinely
  Bool-sorted `ite`, as opposed to the regex-sorted case below).
  Compiles standalone with zero admits.
- **[`Z3RegexExprTheory.fst`](Z3RegexExprTheory.fst)**: `seq_lit` gained a `cond_interp :
  interpretation bool` field and `eval_cond`, used only to give a
  regex-sorted `ite`'s *condition* `c` a concrete truth value (`c` is
  assumed closed; atoms not themselves built from basic connectives
  -- e.g. an opaque string equality -- are treated as propositions
  whose truth `cond_interp` assigns directly, out of scope to model
  more deeply). `to_lang`'s new `ite` case requires *both* branches
  `t`/`f` to be recognized regex expressions (matching that an
  ill-formed `ite` is not well-sorted regardless of which branch a
  model happens to select) and then picks the one `eval_cond` selects
  -- the actual, model-dependent denotation is always exactly one
  branch, never a combination of both.
- **[`Z3RegexInfo.fst`](Z3RegexInfo.fst)**: a new combinator `info_orelse`, mirroring
  `info::orelse`'s real formula precisely -- unlike `info_union`
  (which combines two sub-languages that are *both* actually present
  in the result), here exactly one of `i1`/`i2` describes the real
  (model-dependent) language and `compute_info` cannot evaluate `c` to
  know which, so `nullable` only commits when *both* branches agree
  (an "OR of possibilities" would be unsound), `min_length`/
  `max_length` take the union of the two intervals (sound for
  *either* branch), and `interpreted` is conservatively `false`
  always, matching the real code's own hardcoded (admittedly
  incomplete, per its `// TBD` comment) choice. The new lemma
  `lemma_sound_orelse` states the correspondingly different
  soundness contract: `info_orelse i1 i2` is sound *simultaneously*
  for `l1` and for `l2` individually (not for a combined language),
  which is exactly what is needed since a fixed model's `to_lang`
  picks exactly one of them. `compute_info`'s `ite` case requires
  *both* sub-infos (matching `to_lang`'s new well-formedness
  requirement above, keeping `info_matches`'s "both recognize `e`, or
  neither does" invariant intact), and both main theorems
  (`lemma_compute_info_sound`, `lemma_compute_info_interpreted_sound`)
  were extended with this case (the latter trivially, since
  `interpreted = false` unconditionally for `ite`).

All three files ([`Z3BasicExprTheory.fst`](Z3BasicExprTheory.fst),
[`Z3RegexExprTheory.fst`](Z3RegexExprTheory.fst), [`Z3RegexInfo.fst`](Z3RegexInfo.fst)) still compile cleanly with
zero admits after this extension.

### Still out of scope

- The legacy arg-based `re.loop` form (bounds passed as ordinary
  `expr` arguments rather than `func_decl` parameters).
- `len_abs` is now formalized separately (see the `len_abs` addendum
  below) **and** wired back into `compute_info`'s own `info` record
  as a `la : len_abs` field alongside `[min_length, max_length]` (see
  the "`la : len_abs` field added to `rex::info`" addendum below).
- `is_known()`/`unknown_info` partial-info propagation for binary
  combinators (simplified throughout to strict all-or-nothing `None`
  propagation).
- Conditions mixing genuine sequence-level equalities (`=`/`distinct`
  between `seq a` terms) with Boolean structure are now wired to real
  sequence semantics by `eval_cond`, see the addendum below; any atom
  still not recognized as a basic-family connective or a sequence-
  sorted `=`/`distinct` remains an opaque proposition via
  `cond_interp`.

## Addendum: `len_abs` (`src/util/len_abs.h`/`.cpp`) and [`Z3LenAbsTheory.fst`](Z3LenAbsTheory.fst)

`len_abs` is a separate, lower-level abstraction than `rex::info`'s
plain `[min_length, max_length]` interval: an *ultimately periodic*
set of lengths, `{ n : lo <= n <= hi, (n mod period) in residues }`
(the class's own doc comment, verbatim), used to tighten length
reasoning beyond what a bare interval can express (its header's own
motivating example: `(a^4)*` has length interval `[0, oo)` but every
accepted word's length is actually a multiple of 4).

**[`Z3LenAbsTheory.fst`](Z3LenAbsTheory.fst)** (new file) formalizes this domain and proves
every operation sound against [`Z3RegexTheory.fst`](Z3RegexTheory.fst)'s `lang`:

- `residue_set = nat -> prop` and `len_abs { la_lo; la_hi; la_period;
  la_residues }` model `len_abs.h`'s `(lo, hi, period, residues)`
  fields directly; `gamma` is the concrete set of lengths an
  abstraction denotes, and `la_sound abs l` ("every length `l`'s
  words have is in `gamma abs`") is the periodic-domain analogue of
  [`Z3RegexInfo.fst`](Z3RegexInfo.fst)'s `info_sound`.
- `la_unite`/`la_meet`/`la_opt`/`la_concat` are formalized in full
  generality (arbitrary periods/residues on both operands) and proved
  sound (`lemma_la_unite_sound`, `lemma_la_meet_sound`,
  `lemma_la_opt_sound`, `lemma_la_concat_sound`), matching
  `len_abs.cpp`'s own formulas up to the choice of common modulus:
  this module always combines via the plain *product* of the two
  periods (always a valid common multiple) rather than the real
  code's tighter lcm/gcd-adaptive `common_period` -- a precision-only
  simplification, never a soundness risk. `la_concat`'s residue
  convolution is expressed as a genuine existential (`exists i j. ...`),
  proved via `Classical.exists_intro`/`exists_elim`, the same idiom
  [`Z3RegexTheory.fst`](Z3RegexTheory.fst)'s own `re_concat` is built on.
- `la_star`/`la_plus`/`la_loop` (`lemma_la_star_sound`,
  `lemma_la_plus_sound`, `lemma_la_loop_bounded_sound`,
  `lemma_la_loop_lo_sound`) are sound for *any* period `g` the caller
  can justify via a new predicate `only_multiples_of abs g` ("every
  length `abs` contains is a multiple of `g`"), proved once by
  induction over `re_pow` (`lemma_pow_gcd_period`) and reused by all
  three. This is a deliberate scope reduction: the real
  `len_abs::gcd()` computes the *tightest* such `g` from
  `(lo, hi, period, residues)` alone via a bounded numerical scan (a
  nontrivial periodic-set argument, not reconstructed here);
  `lemma_only_multiples_of_period` discharges the proof obligation
  for exactly the header's own motivating shape -- an abstraction
  whose only possible residue is 0 -- so callers in that common case
  get a ready-made proof, while the general multi-residue `gcd()`
  case (e.g. `(aa)*|(aaa)*`'s period-6, residues `{0,2,3,4}`, gcd 1)
  is left as future work.

[`Z3LenAbsTheory.fst`](Z3LenAbsTheory.fst) compiles cleanly with zero admits.

## Addendum: `la : len_abs` field added to `rex::info`/[`Z3RegexInfo.fst`](Z3RegexInfo.fst)

[`Z3RegexInfo.fst`](Z3RegexInfo.fst)'s `info` record now carries a `la : len_abs` field
alongside `min_length`/`max_length`, and `info_sound` additionally
requires `la_sound i.la l`. Breaking the resulting circular
dependency ([`Z3LenAbsTheory.fst`](Z3LenAbsTheory.fst) needs `ebound`/the `re_pow`-length
lemmas that used to live in [`Z3RegexInfo.fst`](Z3RegexInfo.fst), while [`Z3RegexInfo.fst`](Z3RegexInfo.fst)
now needs `len_abs`) required extracting that shared machinery into a
new leaf module **[`Z3RegexBounds.fst`](Z3RegexBounds.fst)** (`ebound`, `eb_le/add/max/
min/scale`, `lemma_len_concat`, `lemma_len_reverse`,
`lemma_pow_min_length`/`lemma_pow_max_length`/etc.), which both
[`Z3RegexInfo.fst`](Z3RegexInfo.fst) and [`Z3LenAbsTheory.fst`](Z3LenAbsTheory.fst) now depend on independently.

Precision achieved per combinator, mirroring `len_abs.cpp`'s own
formulas:

- **Full precision** (same generality as `len_abs.cpp`'s own
  combinators): `concat` (`la_concat`), `union`/`xor`'s underlying
  union/`ite`'s `orelse` (`la_unite`), `opt` (`la_opt`).
- **Sound but potentially loose periodicity**: `star`/`plus`/`loop`
  use a new, purely computable helper `la_period_for_star` that picks
  period `g = la_lo` when the sub-expression's `la` is already an
  exact singleton (e.g. from a literal `Re_seq_to_re`), recovering the
  header's own `(a^4)*`-style precision in that case, and falls back
  to the always-safe `g = 1` (no periodicity gained) otherwise --
  `len_abs::gcd()`'s general multi-residue period search is not
  reconstructed.
- **Sound via monotonicity only** (no periodicity precision):
  `complement` (`la_trivial`, a plain interval with no residues
  tracked), `inter` (`la_meet` applied to both operands after
  narrowing each to the shared result language via subset
  reasoning), `diff` (reuses the left operand's `la` as-is, since
  `re_diff l1 l2 subseteq l1`).
- `reverse` passes `i.la` through unchanged (sound since
  `len (reverse w) == len w`, [`Z3RegexBounds.fst`](Z3RegexBounds.fst)'s
  `lemma_len_reverse`).

The key enabling lemma for the monotonicity cases is
`lemma_la_sound_monotone` (new, in [`Z3LenAbsTheory.fst`](Z3LenAbsTheory.fst)): an
abstraction sound for `l` remains sound for any `l' subseteq l`.
Applied with [`Z3RegexTheory.fst`](Z3RegexTheory.fst)'s definitional unfoldings of
`re_inter`/`re_diff`/`re_xor` (all plain, non-opaque `let`s), this
lets `inter`/`diff`/`xor`/`orelse` reuse `concat`/`union`-level
combinators without needing dedicated `len_abs` operators for
intersection or difference.

All `lemma_sound_X` lemmas were extended to additionally discharge
the new `la_sound` conjunct of `info_sound`, and
`lemma_compute_info_sound`/`lemma_compute_info_interpreted_sound`
required no structural changes. [`Z3RegexBounds.fst`](Z3RegexBounds.fst),
[`Z3LenAbsTheory.fst`](Z3LenAbsTheory.fst), and [`Z3RegexInfo.fst`](Z3RegexInfo.fst) all compile cleanly from a
fresh `.checked` state with zero admits.

## Addendum: generalizing `la_period_for_star` via a new `la_mult` field

The previous addendum's `la_period_for_star` only recovered a
nontrivial period (`g = la_lo`) for the narrow "exact singleton"
case. [`Z3LenAbsTheory.fst`](Z3LenAbsTheory.fst)'s `len_abs` record now carries an extra
`la_mult : nat` field (`0` ~ "no extra fact known", else a value such
that every length the abstraction contains is provably a multiple of
`la_mult`), propagated compositionally through `unite`/`meet`/
`concat`/`opt`/`star`/`plus`/`loop`, so that chains of these
combinators over already-periodic sub-expressions (not just literal
singletons) can now justify a nontrivial `g` for `star`/`plus`/`loop`.

This generalizes, but deliberately does **not** reconstruct,
`len_abs::gcd()`'s real multi-residue scan: it only ever tracks a
*single* divisor fact per abstraction, propagated via a plain
non-negative `ngcd` (built on `FStar.Math.Euclid.euclid_gcd`), so a
shape like `(aa)*|(aaa)*` (period 6, residues `{0,2,3,4}`, for which
the real algorithm can derive a tighter periodicity than any single
`la_mult` value captures) still has no path to a nonzero `la_mult`
under this design.

Key design points:

- **Soundness invariant `la_mult_sound`** is split by `la_period`:
  for `la_period > 1`, it is a purely *structural*, window-independent
  fact about the residue formula itself (`la_period % la_mult == 0`
  and `forall r < la_period. la_residues r ==> r % la_mult == 0`),
  deliberately avoiding any reference to `la_lo`/`la_hi` -- needed
  because `unite`/`meet`/`concat`'s combined residue formulas can
  admit lengths outside either operand's original window, so a
  window-level argument alone isn't compositional across these binary
  combinators. For `la_period <= 1`, it falls back to the simpler,
  window-level `only_multiples_of` (sufficient for `la_exact n`, which
  sets `la_mult = n`).
- `la_unite`/`la_meet`/`la_concat` propagate `la_mult = ngcd
  mult_a mult_b` when both operands have `period > 1` and a known
  nonzero `la_mult`; `la_opt` propagates `a.la_mult` only when `a`
  itself is already periodic (its `la_period <= 1` set is the *whole*
  `[lo,hi]` interval, not a finite residue set, so reusing `la_mult`
  there would be unsound); `la_star`/`la_plus`/`la_loop` set `la_mult
  = g` directly (already proven a valid period via
  `only_multiples_of`).
- `la_period_for_star abs` is now simply `abs.la_mult` when `> 1`,
  else `1` -- replacing the old singleton-only special case.
- New reusable number-theoretic lemmas: `ngcd`/`lemma_ngcd_is_gcd`
  (built from `FStar.Math.Euclid.euclid_gcd`, handling its
  up-to-sign witness via `lemma_is_gcd_negate`), `lemma_ngcd_dvd_chain_l/_r`
  and `lemma_ngcd_dvd_period_l/_r` (divisibility chaining through a
  gcd), and `lemma_mod_via_period` (`(n % period) % mult == n % mult`
  when `mult` divides `period`, via `FStar.Math.Lemmas.lemma_div_mod`
  + `modulo_modulo_lemma`).

[`Z3RegexInfo.fst`](Z3RegexInfo.fst) required **no changes**: its existing `info_sound`
hypothesis already implies `la_sound i.la l`, which now transitively
carries `la_mult_sound i.la`, and all call sites into
`lemma_la_period_for_star` continue to typecheck unchanged via F*'s
automatic unfolding of these transparent `prop`-valued `let`s. Both
[`Z3LenAbsTheory.fst`](Z3LenAbsTheory.fst) and [`Z3RegexInfo.fst`](Z3RegexInfo.fst) compile cleanly from a
fresh `.checked` state with zero admits.

## Addendum: `eval_cond` wired to real sequence equalities ([`Z3RegexExprTheory.fst`](Z3RegexExprTheory.fst))

Closes the "conditions mixing genuine sequence-level equalities with
Boolean structure" gap listed above: previously `eval_cond` (used by
`to_lang`'s `(ite c t f)` case to pick the actual, model-dependent
branch) evaluated its condition `c` entirely via
`Z3BasicExprTheory.eval_bool sl.cond_interp ...`, which is
monomorphic in a single `value:eqtype` for the whole condition tree
(instantiated at `value = bool` here) -- so a subterm `(= s1 s2)`
where `s1`, `s2 : seq a` could only ever be treated as an *opaque*
Boolean atom by `cond_interp`, never as a real sequence equality,
even though [`Z3RegexExprTheory.fst`](Z3RegexExprTheory.fst) already has its own sound notion
of sequence equality via `eval_leaf`.

`eval_cond` is now a recursive function in its own right (mirroring
`eval_bool`'s structural recursion over `and`/`or`/`not`/`implies`/
`xor`/`ite`/`true`/`false`, via the mutually-recursive helpers
`eval_cond_and`/`eval_cond_or`), with two new cases:

- `(= x y)` where both `x` and `y` are recognized as sequence-sorted
  (`is_seq_sorted`, a new predicate comparing `get_sort` against a
  dedicated marker `seq_sort : sort`, analogous to
  `Z3AstTheory.bool_sort`/`lambda_sort`) is evaluated as
  `eval_leaf sl x = eval_leaf sl y` -- real `seq a` equality.
- `(distinct x1 ... xn)` where the (well-sorted, hence uniformly
  sorted) arguments are sequence-sorted is evaluated as
  `all_distinct` over their `eval_leaf`-images.

Any node `eval_cond` does not itself recognize this way -- an
`=`/`distinct` between non-sequence-sorted arguments, an arity
mismatch, an uninterpreted Boolean atom, or an application from
another family entirely -- falls back to the previous
`eval_bool sl.cond_interp (fun b -> b) e (fun _ -> false)` path
unchanged, so this is a strict extension, not a behavior change, for
every condition that does not itself contain a sequence-sorted
equality/distinctness.

Four new lemmas state and check the soundness payoff:

- `lemma_eval_cond_eq`: a seq-sorted equality condition really does
  reduce to `eval_leaf`-based sequence equality (a definitional
  sanity check).
- `lemma_eval_cond_eq_ground`/`lemma_eval_cond_distinct_ground`: the
  key soundness property -- a seq-sorted equality/distinctness
  condition between two *ground* leaves (`is_ground_leaf`) gets the
  exact same truth value under any two `seq_lit`s that agree on
  classification (`same_classification`), regardless of how they
  otherwise interpret symbolic leaves or `cond_interp`'s atoms. This
  lifts `lemma_eval_leaf_ground`'s model-independence guarantee for
  bare leaves through `eval_cond`, via direct appeal to
  `lemma_eval_leaf_ground` on each argument.
- `lemma_eval_cond_distinct_pairwise`: `distinct` between seq-sorted
  arguments really does demand sequence inequality, mirroring
  `Z3BasicExprTheory.lemma_eval_bool_distinct_pairwise`.

`eval_cond`'s type signature (`seq_lit a -> expr -> bool`) is
unchanged, so `to_lang`'s `Op_ite` case and [`Z3RegexInfo.fst`](Z3RegexInfo.fst)'s
`compute_info`/`lemma_compute_info_sound` required **no changes**.
All files compile cleanly from a fresh `.checked` state with zero
admits.

## Addendum: a general multi-residue `gcd` soundness certificate (`Z3LenAbsTheory.fst`)

Partially closes the "real multi-residue `gcd()` scan" gap noted in
the `len_abs` addendum above: `la_mult`'s combinators only ever
*propagate* a single divisor fact compositionally (`ngcd` of two
already-known `la_mult`s), so a shape like period 6, residues `{2,
4}` -- true gcd 2, but built from no single already-periodic
sub-expression, and with no residue equal to 0 -- was previously
undiscoverable.

New lemma `lemma_only_multiples_of_scan` generalizes
`lemma_only_multiples_of_period` (previously restricted to "the only
possible residue is 0") to an *arbitrary* caller-supplied candidate
`g`: given `abs.la_period % g == 0` and every residue `abs` actually
admits is itself a multiple of `g`, `only_multiples_of abs g` holds
-- exactly the soundness obligation the real `len_abs::gcd()`'s
scanning algorithm's output must discharge, now available as a
standalone, reusable tool rather than only ever being invoked
implicitly with `g = abs.la_period` or `g = abs.la_mult`. New
worked example `la_gcd_example`/`lemma_la_gcd_worked_example`
verifies this recovers the true gcd `2` for the period-6,
residues-`{2,4}` shape above by hand -- exactly what a genuine
multi-residue scan would discover, and exactly what single-divisor
`la_mult` propagation cannot derive.

*Automatically discovering* the tightest such `g` from an arbitrary
`(lo, hi, period, residues)` alone remains unimplemented: it would
additionally require `residue_set = nat -> prop` to be decidable (the
real `uint64_t` bitmask `len_abs.cpp` actually uses), which is a
representation change out of scope for this pass (an earlier attempt
at a fully computable `gcd_scan`/`la_gcd_scan` fold, built on this
module's existing `unfold`-marked `ngcd`, proved soundness-correct
but ran into severe SMT-side blowup from `ngcd`'s forced inlining and
was abandoned in favor of this simpler, still mathematically
meaningful certificate-checking form). `Z3LenAbsTheory.fst` compiles
cleanly from a fresh `.checked` state with zero admits; no other file
needed any change.

## `OP_SEQ_IN_RE` membership and `seq_derive.cpp`'s symbolic derivatives

`str.in_re`/`OP_SEQ_IN_RE` (`seq_rewriter.cpp`'s `mk_str_in_regexp`)
and `src/ast/rewriter/seq_derive.cpp`'s symbolic (Brzozowski)
derivative engine -- built on top of this report's `to_lang`/`lang a`
machinery via two further files, [`Z3SeqDerive.fst`](Z3SeqDerive.fst)
and [`Z3RegexMembership.fst`](Z3RegexMembership.fst) -- are a
different subject (`seq_rewriter.cpp`/`seq_derive.cpp`, not
`seq_decl_plugin.cpp`'s `get_info`), and are now reported in full in
[`SEQ_REWRITER_REPORT.md`](SEQ_REWRITER_REPORT.md)'s "Part 2".
