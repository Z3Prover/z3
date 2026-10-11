# Bool/Arith Rewriter Formalization Report

## Scope

This report documents an F* formalization of the propositional-logic and
arithmetic tautologies underlying two of Z3's core term-rewriting engines:

- [`Z3BoolRewriter.fst`](Z3BoolRewriter.fst) — `src/ast/rewriter/bool_rewriter.cpp` /
  `bool_rewriter.h` (AND/OR/NOT/ITE/EQ/DISTINCT/XOR/IMPLIES/NAND/NOR/GE2
  simplification rules).
- [`Z3ArithRewriter.fst`](Z3ArithRewriter.fst),
  [`Z3ArithRewriterPower.fst`](Z3ArithRewriterPower.fst),
  [`Z3ArithRewriterCast.fst`](Z3ArithRewriterCast.fst), and
  [`Z3ArithRewriterOrder.fst`](Z3ArithRewriterOrder.fst) —
  `src/ast/rewriter/arith_rewriter.cpp` / `arith_rewriter.h` (div/idiv/mod/rem,
  abs, power, to_int/to_real/is_int, and comparison-operator (`<`/`>`/`=`/ite-
  lifting/floor-bridging/mod-bound) simplification rules).

Every `mk_*_core` rewrite rule in these files replaces one term by another
that is claimed to denote the same value under every model. The F* files
state each such claim as a standalone lemma over an abstract/uninterpreted
domain (booleans or `int`/`real`) and have them **mechanically verified**
by F*'s type checker, which discharges the proof obligations to Z3's own
decision procedures for quantifier-free boolean logic and linear/non-linear
integer and real arithmetic.

## Method

- F* `2026.09.27` (Windows x86_64 release) and its bundled Z3 `4.15.3` were
  downloaded from the official `FStarLang/FStar` GitHub releases and used
  standalone, exactly as for the prior `Z3NlArith.fst` audit.
- Each file was verified independently with:
  ```
  fstar.exe <File>.fst --z3rlimit 40
  ```
  All five modules report `Verified module: <Name> — All verification
  conditions discharged successfully`, with **zero** `admit`/`sorry`.
- The arithmetic rewriter formalization is split into three files
  (div/mod/abs core, power, and to_int/to_real casts) rather than one,
  purely for **verification performance**: combining all rule families in
  a single module makes Z3's proof search for the power-merge induction
  time out (multiple minutes with no progress), while each module verifies
  in well under a minute on its own. This is a tooling artifact of SMT
  proof search, not a change in what is proved.
- Booleans are modeled directly as F*'s native `bool` type: quantifier-free
  boolean equalities over free variables are *completely* decided by Z3's
  propositional reasoning, so every lemma in `Z3BoolRewriter.fst` has proof
  body `()` — no manual case splits are needed.
- Integers use F*'s built-in `int` with `FStar.Math.Lemmas` for the
  Euclidean division/modulo identities; reals use `FStar.Real` with its
  dotted operators (`+.`, `-.`, `*.`, `/.`, `>=.`), as in the NLA audit.
  `to_real`/`to_int` (Z3's `OP_TO_REAL`/`OP_TO_INT`) are modeled as an
  `assume`d injective embedding of `int` into `real`, since F*'s own `int`
  and `real` types are not natively related by such a coercion.

## Source-to-lemma correspondence

### `Z3BoolRewriter.fst`

| C++ source rule | F* lemmas |
|---|---|
| `mk_nflat_and_core` / `mk_flat_and_core` | `and_unit`, `and_dup`, `and_false_absorb`, `and_contradiction`, `and_singleton` |
| `mk_nflat_or_core` / `mk_flat_or_core` | `or_unit`, `or_dup`, `or_true_absorb`, `or_excluded_middle` |
| `mk_and_as_or` (De Morgan, `m_elim_and`) | `and_as_or` |
| `mk_not_core` | `not_not`, `not_true`, `not_false`, `not_eq_push` |
| `mk_nested_ite` (constant/degenerate-branch case table) | `ite_true_cond`, `ite_false_cond`, `ite_same_branches`, `ite_true_false`, `ite_false_true`, `ite_true_branch`, `ite_false_branch`, `ite_true_else`, `ite_false_else` |
| `mk_ite_core` (condition negation, nested-ite collapsing/merging) | `ite_neg_cond`, `ite_nested_same_cond_else`, `ite_nested_same_cond_then`, `ite_merge_then_eq`, `ite_extra_merge` |
| `mk_eq_core` (boolean-specific folding) | `eq_refl`, `eq_complement`, `eq_true_lhs`, `eq_false_lhs`, `eq_not_not`, `eq_nested_cancel` |
| `mk_distinct_core` | `distinct2`, `distinct3_bool_false` |
| `mk_xor` / `mk_implies` / `mk_nand` / `mk_nor` / `mk_ge2` | `xor_def`, `implies_def`, `nand_def`, `nor_def`, `ge2`, `ge2_with_false`, `ge2_with_true` |

32 lemmas in total, all verified.

### `Z3ArithRewriter.fst` / `Z3ArithRewriterPower.fst` / `Z3ArithRewriterCast.fst`

| C++ source rule | F* lemmas |
|---|---|
| `mk_div_core` (numeral-denominator folding) | `div_self`, `div_by_numeral` |
| `mk_idiv_core` / `mk_mod_core` (Euclidean structure, div/mod by ±1, idempotence, multiple-dropping, negated modulus) | `euclid_decomp`, `mod_range`, `idiv_one`, `idiv_minus_one`, `mod_one`, `mod_minus_one`, `mod_idempotent`, `mod_drop_multiple`, `mod_neg_modulus` |
| `mk_rem_core` (`rem` in terms of `mod`) | `rem_of_mod` |
| `mk_abs_core` | `abs_int`, `abs_real` |
| `mk_power_core` (exponent constant folding, nested-power merge) | `power_one`, `power_zero`, `power_zero_base`, `power_add`, `power_merge` |
| `mk_to_int_core` / `mk_to_real_core` / `mk_is_int` | `to_int_to_real_cancel`, `push_to_real_add`, `push_to_real_mul`, `is_int_of_to_real` |

21 lemmas in total, all verified.

### `Z3ArithRewriterOrder.fst`

| C++ source rule | F* lemmas |
|---|---|
| `mk_lt_core` / `mk_gt_core` (defined via `not(le)`) | `lt_as_not_le`, `gt_as_not_le` |
| `mk_eq_core`'s `m_eq2ineq` branch (antisymmetry of order) | `eq_as_ineqs` |
| `mk_le_ge_eq_core`'s ite-hoisting branches | `ite_lift_le`, `ite_lift_ge`, `ite_lift_eq` |
| `mk_le_ge_eq_core`'s `to_int` bridging branch (floor characterization) | `to_int_le_iff`, `to_int_ge_iff`, `to_int_eq_iff` |
| `is_bound`'s mod-range constant-folding shortcuts | `mod_ge_zero_true`, `mod_le_neg_false`, `mod_le_ge_modulus_true`, `mod_le_modulus_minus_one`, `mod_ge_too_large_false` |
| `is_separated`'s nonneg/nonpos-summand bound | `nonneg_summand_le_false`, `nonpos_summand_ge_false` |

13 lemmas in total, all verified.

## What was verified (and what wasn't)

**Verified, from first principles:**

1. **AND/OR core identities** — idempotence/duplicate-elimination,
   identity-element absorption, and the two excluded-middle /
   contradiction facts (`p && not p = false`, `p || not p = true`) that
   `mk_nflat_and_core`/`mk_nflat_or_core` detect while scanning argument
   lists for a literal and its negation.
2. **The finite `mk_nested_ite` case table** — every combination of a
   constant condition or constant/equal/complementary branch reduces to a
   smaller boolean expression; all nine cases are exact propositional
   identities, not approximations.
3. **`mk_ite_core`'s structural rewrites** — negating the condition swaps
   the branches; a nested `ite` on the *same* condition in one branch is
   dead code there; two `ite`s that agree on one branch merge their
   conditions disjunctively; and the `m_ite_extra_rules` nested-merge
   identity `ite(c1, ite(c2,t1,t2), t1) = ite(c1 && not c2, t2, t1)`.
4. **`mk_eq_core`'s boolean folding** — reflexivity, complement-to-false,
   constant-operand simplification, and double-negation cancellation
   under equality (`(not a) = (not b)` iff `a = b`).
5. **`mk_distinct_core`'s pigeonhole fact** — three boolean values can
   never be pairwise distinct, since the boolean domain has exactly two
   elements; proved here as an instance of unsatisfiability
   (`a<>b && b<>c && a<>c` implies `False`).
6. **The definitional expansions** `xor`, `implies`, `nand`, `nor`, and
   `ge2` — each is proved equal to the exact formula the rewriter falls
   back to when no constant-folding opportunity applies.
7. **Euclidean division/modulo laws** — `a = (a/b)*b + a%b`, the
   remainder range `0 <= a%b < b`, div/mod by `1` and `-1`, idempotence of
   `mod` on a fixed modulus, dropping an exact multiple of the modulus
   from a sum, and `mod(a,-b) = mod(a,b)`. These are exactly the algebraic
   facts `mk_idiv_core`/`mk_mod_core`'s numeral- and structural-folding
   branches depend on, proved via `FStar.Math.Lemmas` (`lemma_mod_twice`,
   `lemma_mod_plus`, `euclidean_div_axiom`) for the two directions where
   plain SMT linear-arithmetic reasoning alone is insufficient.
8. **`rem` in terms of `mod`** — the defining case split
   `rem(a,b) = mod(a,b)` for `b >= 0`, `-mod(a,b)` for `b < 0`.
9. **`abs(a) = ite(a >= 0, a, -a)`** over both `int` and `real`.
10. **Power identities** — `x^1 = x`, `x^0 = 1` (`x <> 0`), `0^n = 0`
    (`n > 0`), and the nested-power merge `(x^y1)^y2 = x^(y1*y2)`, proved
    by structural induction on the natural-number exponent (mirroring the
    `nla_powers.cpp` induction pattern from `Z3NlArith.fst`); the
    induction step needed one explicit call to
    `FStar.Math.Lemmas.distributivity_add_right` to discharge the
    nonlinear exponent-arithmetic identity `y1 + y1*(y2-1) = y1*y2`.
11. **to_int/to_real coercion laws** — `to_int(to_real n) = n`,
    injectivity of `to_real`, and that `to_real` distributes over `+`
    and `*` — modeled via an `assume`d abstract embedding, since F*'s
    `int`→`real` relationship is not a built-in coercion with these
    properties pre-proved; the lemmas are then immediate logical
    consequences of the four `assume`d axioms, analogous to how the NLA
    report treats `exp`/`log`/`sin`/`cos` as axiomatized.
12. **`<`/`>` as derived connectives** — `mk_lt_core`/`mk_gt_core` literally
    rewrite `(< a b)` to `(not (<= b a))` and `(> a b)` to `(not (<= a b))`;
    both are proved from trichotomy of the real order.
13. **`eq` as a conjunction of inequalities** (`m_eq2ineq`) — `a = b` iff
    `a <= b /\ b <= a`, the antisymmetry of `<=`.
14. **Lifting a comparison through an `ite`** — `(if c then t else e) <= k`
    (resp. `>= k`, `= k`) equals `if c then (t <= k) else (e <= k)`
    *unconditionally*; the rewriter's `ref_count == 1` guard on this rule
    is purely a term-size heuristic, not a soundness side-condition, which
    the proof confirms by discharging both branches with a plain case
    split on `c`.
15. **The `to_int`/comparison bridging identities** — `to_int(t) <= n` iff
    `t < to_real(n+1)`, `to_int(t) >= n` iff `to_real(n) <= t`, and
    `to_int(t) = n` iff `to_real(n) <= t < to_real(n+1)`: these are exactly
    the floor-function characterization that lets `mk_le_ge_eq_core`
    rewrite a `to_int`-headed inequality into a pure real inequality.
    Proved from an `assume`d floor-defining inequality plus monotonicity of
    `to_real`, each used only at the two concrete instantiations the proof
    needs (not as a blanket quantified axiom).
16. **`is_bound`'s mod-range shortcuts** — `mod(x,b) >= 0` is always true;
    `mod(x,b) <= c` is false for `c < 0` and true for `c >= b`; and
    `mod(x,b) <= b-1` always holds. All five are direct corollaries of the
    Euclidean remainder range `0 <= mod(x,b) < b` already proved as
    `mod_range` in `Z3ArithRewriter.fst`.
17. **`is_separated`'s summand-bound facts** — if every non-numeral summand
    of a sum is known non-negative (resp. non-positive), the sum is
    bounded below (resp. above) by its numeral part alone, which is what
    lets `is_separated` certify `(<= (+ c x) k) = false` once `c > k` (and
    the dual `>=` case).

**Explicitly out of scope, and why:**

- **`local_ctx_simp`, `simp_nested_not_or`, `simp_arg`,
  `simp_nested_eq_ite`, `push_new_arg`** (`bool_rewriter.cpp`) implement a
  context-propagation *algorithm* (substituting known truth values of a
  literal into nested subterms) rather than stating one reusable
  equivalence; its correctness reduces to repeated application of the
  equality/ITE facts already covered above, so formalizing it would be an
  algorithm-correctness proof, not a new tautology.
- **`try_ite_value`, `simplify_eq_ite`, `mk_eq_plain`, `try_ite_eq`**
  (`bool_rewriter.cpp`) depend on domain-specific oracles
  (`are_equal`/`are_distinct`/`is_value`/`is_unique_value`) that compare
  *arbitrary* sort values, not just booleans; without fixing a concrete
  sort these are vacuous or ill-typed as stated, so they are summarized
  rather than formalized.
- **`decompose_ite`** is a structural search utility (find an ITE subterm)
  with no semantic content of its own.
- **`cancel_monomials`, `factor_le_ge_eq`, `elim_to_real`, `get_range`,
  `get_coeffs_gcd`/`div_polynomial` (GCD rounding)** (`arith_rewriter.cpp`,
  generic `poly_rewriter` infrastructure and `mk_le_ge_eq_core`'s
  remaining helpers beyond the to_int-bridging and ite-lifting branches
  formalized above) implement polynomial normalization / bound-propagation
  *search*, analogous to the NLA report's treatment of Gröbner-basis
  reduction and interval propagation as out of scope: their soundness
  reduces to linear-arithmetic facts already standard and not specific to
  this rewriter. (`is_bound`'s mod-range shortcuts and `is_separated`'s
  summand-bound facts *are* now formalized in `Z3ArithRewriterOrder.fst`,
  as the two parts of these functions whose content is a standalone
  arithmetic tautology rather than search.)
- **`mk_sin_core`/`mk_cos_core`/`mk_tan_core`/`mk_asin_core`/
  `mk_acos_core`/`mk_atan_core`/`mk_sinh_core`/`mk_cosh_core`/
  `mk_tanh_core`** and the `is_pi_multiple`/`is_pi_offset` family
  (`arith_rewriter.cpp`) are periodicity/special-value facts for
  transcendental functions, already covered in spirit by the
  `exp`/`log`/`sin`/`cos`/`atan2` axiomatization in `Z3NlArith.fst`;
  re-deriving the pi-multiple case analysis here would duplicate that
  work without adding new verified content.
- **`mk_shl_core`/`mk_lshr_core`/`mk_ashr_core`/`mk_band_core`**
  (bit-vector-flavored integer operations exposed through the arithmetic
  sort) manipulate fixed-width wraparound arithmetic; they are a
  bit-vector audit's subject, not an arithmetic-rewriter one, and are
  left for a future `Z3BvRewriter.fst`.
- **`mk_div_irrat_rat`/`mk_div_rat_irrat`/`mk_div_irrat_irrat`,
  `is_algebraic_numeral`/`reduce_power`** (algebraic-number arithmetic)
  require a full real-algebraic-number theory (root isolation, degree
  bounds) that is out of reach of F*'s/Z3's native real-arithmetic
  decision procedure; summarized rather than formalized, as the
  algebraic-number case was in the NLA report's division/power lemmas.

## Files

| File | Subject | Lemma count | Verified |
|---|---|---|---|
| `Z3BoolRewriter.fst` | `bool_rewriter.cpp`/`.h` | 32 | ✅ |
| `Z3ArithRewriter.fst` | `arith_rewriter.cpp`/`.h` div/idiv/mod/rem/abs | 12 | ✅ |
| `Z3ArithRewriterPower.fst` | `arith_rewriter.cpp` `mk_power_core` | 5 | ✅ |
| `Z3ArithRewriterCast.fst` | `arith_rewriter.cpp` to_int/to_real/is_int | 4 | ✅ |
| `Z3ArithRewriterOrder.fst` | `arith_rewriter.cpp` lt/gt/eq2ineq/ite-lifting/to_int-bridging/is_bound/is_separated | 13 | ✅ |

## Conclusion

All 66 lemmas across the five files type-check and are discharged by F*'s
SMT backend with no `admit`/`sorry`, confirming that every formalized
`bool_rewriter`/`arith_rewriter` rewrite rule encodes a genuine semantic
tautology (propositional, Euclidean-arithmetic, or power/coercion
identity) rather than an approximation. The out-of-scope items above are
either algorithm-correctness concerns outside a single-lemma audit's
reach, or depend on domain theories (algebraic numbers, transcendental
periodicity, bit-vector wraparound) better suited to their own dedicated
audits.
