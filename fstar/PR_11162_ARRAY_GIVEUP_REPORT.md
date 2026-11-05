# Audit: PR #11162 — "Avoid array-theory give-up for uninterpreted uses of lambdas"

## Summary

`theory_array_full`'s lambda-use "give-up" classifier
(src/smt/theory_array_full.cpp, ~line 1039) walks every parent
application `p` of a `lambda`-denoted array enode `n` and conservatively
reports incompleteness unless `p` is one of five recognized shapes
(`is_default`/`is_select`/`is_array_ext`/`ctx.is_beta_redex`/
`is_supported_array_eq`) — each of which requires inspecting `n`'s
lambda body (beta-reduction or extensionality-witness instantiation).

**Bug** (issue #11154): a parent `p` that is simply an application of
an *uninterpreted* function `g(n)` matched none of the five shapes, so
it was flagged as unsupported, forcing a give-up (`unknown`,
"(incomplete (theory array))") even though congruence closure — the
only reasoning `g`'s theory ever needs — never inspects `n`'s internal
representation, only its equivalence class.

**Fix**: the one-line addition of `!is_uninterp(p->get_expr())` to the
guard.

## Formalization

[`Z3ArrayGiveUp.fst`](Z3ArrayGiveUp.fst) models the classifier over an
abstract enumeration `shape` of the parent-application cases it
distinguishes (`Default | Select | ArrayExt | BetaRedex | SupportedEq |
Uninterp | Other`), transcribing `old_unsupported`/`new_unsupported`
verbatim from the boolean condition. Three theorems:

1. **`lemma_new_narrows_old`**: anything the new classifier still flags
   was already flagged by the old one — the fix is a pure narrowing of
   the give-up set, never a widening (it cannot introduce a new
   unsound silent success by *adding* a previously-caught case).
2. **`lemma_differ_only_at_uninterp`** / **`lemma_agree_off_uninterp`**:
   the two classifiers disagree *exactly* at `Uninterp` and agree
   everywhere else — the formal counterpart of the PR's single-
   condition, one-line diff.
3. **`lemma_other_still_unsupported`**: the catch-all `Other` case (any
   parent shape the theory has no handling for at all) remains flagged
   by both classifiers — confirming the fix does not quietly widen the
   set of "safe" shapes beyond the one specifically justified case.

All three are discharged by direct case analysis over the 7-constructor
`shape` type.

## Semantic justification (informal)

A closing comment in the `.fst` file (not mechanically checked, in the
same spirit as this series' other "honest limitation" notes) explains
*why* excluding `Uninterp` is safe: every one of the five originally-
recognized shapes needs to inspect `n`'s lambda body to be handled
correctly; an uninterpreted-function parent needs nothing beyond
congruence (`n ~ n' ⟹ g(n) ~ g(n')`), which is parametric in `n`'s
*equivalence class*, never its internal representation. Whatever
axiom-instantiation accounting `n` requires is driven by its *other*
occurrences (a `select`/`store`/`=`), which remain separately and
unconditionally subject to the still-active original five checks —
exactly matching issue #11154's regressed benchmark, whose lambda array
is read via `select` elsewhere and *also* passed to an uninterpreted
function.

## Scope / what is *not* modeled

A full soundness/completeness proof of `theory_array_full.cpp`'s model
construction is out of scope, consistent with every other `theory_*`
decision-procedure file in this audit series (these are solver-
engineering completeness heuristics, not rewrite rules with a crisp
input/output specification). This audit targets precisely the boolean
classifier that is the entirety of PR #11162's `.cpp` diff.

## Verification

```
C:\fstar\fstar\bin\fstar.exe --smt C:\z3-4.13.3\z3-4.13.3-x64-win\bin\z3.exe Z3ArrayGiveUp.fst
```
produces `Verified module: Z3ArrayGiveUp` / all verification conditions
discharged successfully. No `admit`/`assume`/axioms.

## Conclusion

PR #11162's fix is **formally confirmed to be a strict, precisely
located narrowing** of the give-up classifier's unsupported-shape set,
touching only the `Uninterp` case and leaving every other recognized
or unrecognized shape's give-up behavior unchanged.
