# F* Formalization of `src/ast/rewriter/pb_rewriter.cpp` — Coverage Report

See [`README.md`](README.md) for the top-level index of this F*
formal-verification audit series.

`pb_rewriter.cpp` (plus its template helper `pb_rewriter_def.h`) is Z3's
pseudo-Boolean (PB) constraint normalizer: it rewrites `(_ at-most-k ...)`
/ `(_ at-least-k ...)` / `pbeq`/`pble`/`pbge` applications — a linear
inequality `c_1*l_1 + ... + c_n*l_n (>=|<=|=) k` over Boolean literals with
rational coefficients — into a normal form (unit coefficients where
possible, merged/coalesced literals, detected tautologies/contradictions)
and, when the result is small or structurally simple enough, directly into
a Boolean combination (`mk_or`/`mk_and`) of the literals. This is a
**first pass**: it formalizes the central truth-preserving identities that
justify `unique`/`normalize`'s core steps and `mk_app_core`'s two
"special case" final rewrites, deferring the gcd-based cutting-plane
reduction, the coefficient-range normalization heuristic, and the general
(non-unit) slack-based conjunction/disjunction/recursive construction to a
follow-up pass.

Proof file: [`Z3PbTheory.fst`](Z3PbTheory.fst).

Toolchain used: [F*](https://github.com/FStarLang/FStar) `v2026.09.27`
(Windows x64) with Z3 `4.13.3` as the SMT backend:

```
C:\fstar\fstar\bin\fstar.exe --smt C:\z3-4.13.3\z3-4.13.3-x64-win\bin\z3.exe Z3PbTheory.fst
```

Type-checks and discharges all verification conditions with **no
`admit`/`assume`/axioms**.

## Representation

A PB constraint is modeled as a `list (int & bool)` — one `(coefficient,
literal-value)` pair per term — plus a threshold `k:int`. `pb_sum` sums
`term_val c x = if x then c else 0` across the list, mirroring the `.cpp`'s
own "coefficient times 0/1-valued literal" semantics (`rational` is
specialized to `int`, matching `normalize`'s own post-"ensure all
coefficients are integers" invariant). `coeff_sum` is the sum of
coefficients alone — the value of the constraint under the all-true
assignment, used as the natural upper bound on `pb_sum`.

## Coverage by rewrite rule

| `.cpp`/`.h` site | Rewrite / identity | Lemma | Status |
|---|---|---|---|
| `unique` (negative-coefficient literal) | `c*l + rest >= k  <=>  (-c)*(not l) + rest >= k - c` | `lemma_negate_flip` | ✅ |
| basic bound | `pb_sum >= 0` for nonnegative coefficients | `lemma_pb_sum_nonneg` | ✅ |
| basic bound | `pb_sum <= coeff_sum` for nonnegative coefficients | `lemma_pb_sum_le_total` | ✅ |
| `normalize` (`k <= 0` tautology detection) | constraint is a tautology | `lemma_trivial_true` | ✅ |
| `normalize` (`sum of coefficients < k` infeasibility detection) | constraint is unsatisfiable | `lemma_trivial_false` | ✅ |
| `normalize` ("tight inequality", `sum == k`) / `mk_app_core` (`slack == k`, `all_unit && k == sz`, `mk_and`) | `pb_sum >= coeff_sum <=> all literals true` (strictly positive coefficients) | `lemma_tight_iff_all_true` | ✅ |
| `mk_app_core` (`all_unit && k.is_one()`, `mk_or`) | `pb_sum >= 1 <=> some literal true` (unit coefficients) | `lemma_unit_at_least_one` | ✅ |
| `normalize` ("ensure the largest coefficient is not larger than `k`") | capping one term's coefficient down to `k` preserves the constraint's truth value against a nonnegative remainder | `lemma_cap_single` / `lemma_cap_head` | ✅ |

## Not yet covered (deferred to follow-up passes)

- **gcd-based cutting-plane reduction** (`normalize`'s `g = gcd(...)`
  step, e.g. `5x + 5y + 2z + 2u >= 5` → `3x + 3y + z + u >= 3`): a genuine
  Diophantine strengthening argument (dividing by the gcd of "slack"
  coefficients and taking a ceiling on `k`), not yet modeled.
- **Coefficient-range normalization** (the `k/n <= ... < k/(n-1)` heuristic
  collapsing all coefficients to `1` when they all fall in a provably-safe
  range): not yet modeled.
- **`mk_app_core`'s general (non-unit) case**: the iterative loop
  computing `slack`, forcing literals into `conj` when `slack < c_i + k`
  (so the literal *must* be true for satisfiability), collecting
  `disj` candidates, and re-packaging the remainder as a (recursive)
  `m_util.mk_ge` constraint. This is the most algorithmically interesting
  part of the file and is deferred; the two special-case final branches
  it falls back to (`mk_or`/`mk_and`) are, however, already covered above.
- **`translate_pb2lia`/`mk_validate_rewrite`/`validate_rewrite`**: these
  build an SMT-LIB2 self-check query (asserting the PB constraint and its
  LIA translation disagree, then dumping it for external validation via
  `TRACE(pb_validate, ...)`) — debugging/validation infrastructure, not
  itself a rewrite rule, so out of scope.
- **`unique`'s sort-and-coalesce step** for *distinct* AST literals that
  happen to be the same underlying atom: the coalescing arithmetic itself
  (`args[i].second += args[j].second`) is just addition of coefficients
  for the same literal value, a trivial corollary of linearity of
  `pb_sum`, not separately proved as a dedicated lemma.

## Summary

This first pass proves 8 lemmas establishing that the core
normalization steps of `unique`/`normalize` and the two Boolean-result
special cases of `mk_app_core` (`mk_or` for unit/`k=1`, `mk_and` for
tight/`k=sz` constraints) preserve the truth value of the PB constraint
for every Boolean assignment. The gcd-based cutting-plane reduction, the
coefficient-range heuristic, and the general slack-based
conjunction/disjunction/recursive construction are catalogued above for a
follow-up pass.
