# Audit: PR #11164 — "Fix MBQI returning `unknown` on array model values over uninterpreted sorts"

## Summary

`array_rewriter::mk_eq_core` (src/ast/rewriter/array_rewriter.cpp,
~line 957) compares `(= lhs rhs)` where both sides are a chain of
`store`s on a `(as const S) v`/`(as const S) w` base, over an array
sort `S` with an *uninterpreted* index domain. Since the domain may be
infinite, the general case must fall back to `expand_store` (turning
each chain into an explicit `lambda`) plus a direct array `=`, which
`mk_eq`/MBQI then discharges via the array extensionality axiom — a
universally-quantified formula over the whole index sort.

**Bug** (issue #11156): this quantifier-introducing fallback fired
*unconditionally* whenever both sides were const-with-stores over an
uninterpreted domain — even when every store index on *both* sides was
already a concrete model value. That is precisely the situation that
arises during MBQI's own array-model reconstruction: MBQI, asked to
re-verify a quantifier it just introduced over values it already fully
knows, could give up (`unknown`, "(incomplete (theory array))") on a
query that is in truth fully decidable without any quantifier at all.

**Fix**: a `has_value_indices` guard (checking `m().is_value(...)` on
every store index in both chains) excludes this branch when all
indices are concrete, letting control fall through to the existing
quantifier-free pointwise comparison machinery further down in the
same function.

## Formalization

[`Z3ArrayGroundIndexEq.fst`](Z3ArrayGroundIndexEq.fst) builds on the
existing extensional array model (`Z3ArrayTheory.fst`'s `arr idx v =
idx ^-> v`) and formalizes the precise semantic fact that justifies the
fix. A store chain is modeled as a list of `(index, value)` update
pairs folded onto a constant base (`chain`), with list head = most
recent `store` (so it shadows earlier pairs at the same index, matching
real `store` semantics for repeated indices).

- **`lemma_chain_off_indices`**: off a chain's own explicit indices, it
  always reads back as its base constant — nothing changed there.
- **`lemma_ground_chain_eq_iff_finite_check`** (the main theorem): two
  chains over bases `base1`/`base2` are fully extensionally equal
  (`feq`, i.e. the actual array-theory `=`) **iff** the bases agree and
  the chains agree at every index mentioned in *either* chain — a
  finite, explicit, syntactically available list. No quantification
  over any index outside this list — in particular, none over the
  (possibly uninterpreted/infinite) domain at large — is logically
  required.
- **`lemma_ground_chain_eq_implies_finite_check`**: the converse
  direction, completing the "iff", recorded for honesty though not
  needed by the rewrite's soundness argument.

This is exactly the fact that licenses `has_value_indices`: when every
index is a concrete value, the equality can be decided by a finite
conjunction of value comparisons plus one base-equality check — the
general quantified-extensionality rewrite is logically unnecessary
(not merely "usually avoidable"), so skipping it loses no soundness.

## Scope / what is *not* modeled

The rewriter's companion `has_large_domain`/`domain_is_larger_than`
size-threshold heuristics (which decide, for *non*-uninterpreted finite
domains, when a similar case-split-vs-quantifier trade-off is worth
making) are not re-examined here — they are orthogonal to this bug
(which is specifically about *uninterpreted* domains, where no
threshold heuristic applies at all, only the strict dichotomy between
"concrete indices" and "fall back to extensionality"). This audit
targets exactly the one condition added by PR #11164's diff.

## Verification

```
C:\fstar\fstar\bin\fstar.exe --smt C:\z3-4.13.3\z3-4.13.3-x64-win\bin\z3.exe Z3ArrayGroundIndexEq.fst
```
produces `Verified module: Z3ArrayGroundIndexEq` / all verification
conditions discharged successfully. No `admit`/`assume`/axioms.

## Conclusion

PR #11164's fix is **formally confirmed sound**: the finite-check
equality it falls through to is provably equivalent to full array
extensionality precisely when all indices are concrete model values,
so excluding this case from the quantifier-introducing branch costs
nothing in soundness while removing an unnecessary, MBQI-defeating
quantifier.
