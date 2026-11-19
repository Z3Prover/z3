# F* audit, PR #11644 @ e72f1ea6656cc3a12b1bf0f8f98484eee43db3c9 (base 1e136dcdeac7bb76b999b81ee3f52a0da9ffbff9)

**Scope (partial):** 3 changed behaviors selected: (1) `context::internalize_quantifier` generated-skolem clause (src/smt/smt_internalizer.cpp, hunk ~L669-679 at head); (2) `ast_manager::update_quantifier_skid` / `compare_nodes` skid comparison (ast.cpp); (3) array_rewriter `mk_eq_core` tagging. Only (1) was given F* obligations; (2) and (3) are manually reviewed only.

## Obligations (module GenQuantSkolem.fst)
- O1 clause `q \/ ~body[sk]` is satisfiable for some skolem interpretation (non-empty sort): **proved**
- O2 if q holds, clause holds for any skolem values (positive polarity adds no constraint): **proved**
- O3 if q false, a falsifying witness exists (negative polarity is realisable): **proved**
- O4 var_subst std_order index arithmetic (decl i <-> skolems[i]): **proved** (pure arithmetic, trivial)

No counterexample was sought-and-found; refutation attempts were not exhaustive.

## Correspondence / assumptions
`q` models forall; `body` models the body as a predicate on one sort (multi-binder follows by tupling, not modelled). Skolem constants are fresh, so existentially interpretable (standard conservative-extension argument; sorts assumed non-empty, true for Z3 sorts). Inherits only F* standard library axioms. Not modelled: C++ execution, `internalize(body,true)` side effects, mk_gate_clause scoping under push/pop (the PR's test covers push/pop), memory safety, generations/relevancy, hash-consing.

## Exclusions
Manually reviewed only, not mechanized: skid in `compare_nodes` (distinct skid => distinct AST nodes, intended; may reduce sharing for quantifiers differing only in skid); update_quantifier_skid copy fidelity (all fields passed through); both array_rewriter tags; tests; simplifier expectation. Unmodelled risk: fresh constants created on every internalization of a generated quantifier (including after pop/re-internalization) may grow terms; model-finder/MBQI interaction with the added clause not examined.

## Reproduce
`timeout 120 /tmp/gh-aw/fstar/bin/fstar.exe --smt /tmp/gh-aw/fstar/lib/fstar/z3-4.13.3/bin/z3 --z3version 4.13.3 --z3rlimit 10 --include /home/runner/work/z3/z3/fstar --cache_dir cache --odir out GenQuantSkolem.fst` (F* 2026.09.27, Z3 4.13.3 pinned). Source snapshot sha256 of head smt_internalizer.cpp is not usable as the saved file was an API JSON envelope; line ranges were taken from the PR patch.
