# F* audit PR 11554 @ 86cec18b3477a5ace02713b56eb671161d47c07d (base 784b613b)

**Scope (partial):** 1 of the changed behaviours: `ite_rewrite` in `fstar/Z3SortedProof.fst` (head lines ~1535-1545, 1780-1800), which accepts premise-free RewriteRule equations satisfying `NR.ite_rewritten` (fstar/Z3NnfReplay.fst head L441-448, sha256 7b9a5d2d...f834; Z3SortedProof.fst sha256 5274eed1...41f2). It is applied without a Real-schema gate, so soundness in every model is the risky claim.

## Obligations
1. Swap law (`ite_swapped`): ite c x y = ite c' y x when c' = not c (or c = not c', by double negation): **proved**.
2. Then-merge (`ite_merged_then`): ite c x (ite c2 x y2) = ite c' x y2 with c' = or [c;c2] or or(junctands c @ junctands c2): **proved** (disj_append).
3. Else-merge (`ite_merged_else`): dual with and: **proved** (conj_append).
No counterexample attempted succeeded: the laws are valid for every sort 'a.

## Correspondence
`ite` = T.Choice evaluation; `disj`/`conj` = n-ary Or/And fold; list append = `joined`'s flattening. `IteLawsAudit.fst` is an abstract self-contained model, NOT an import of the PR modules. Syntactic guards (same declaration f, equal branches x2=x / y2=y, shallow, negation_of, scoping, sort agreement via Choice classification) are NOT mechanized here; they are manually read from the source: they appear to force same f (hence same result sort) and exact branch equality. Mechanical proof checking of the PR's own lemmas (lemma_ite_rewritten_at etc.) was not run.

## Assumptions
Boolean conditions evaluate to bool; junctand of a non-nary condition is a singleton; standard F* library only. No admit/assume.

## Exclusions
Not audited: real_farkas, real_rewrite, Z3SortedReal*, Z3SortedRealLinear/Root/Extension, nnf_verdict/replay_with changes, lemma_full_extension_real, needs_real_semantics, test files, tools (OCaml/Python), docs. C++ execution, AST plumbing and memory safety are outside this semantic audit.

## Reproduce
See verification_log. F* 2026.09.27, Z3 4.13.3 (pinned release backend).
