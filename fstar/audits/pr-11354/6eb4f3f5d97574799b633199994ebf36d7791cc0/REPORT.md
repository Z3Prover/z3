# Audit PR #11354 @ 6eb4f3f5d97574799b633199994ebf36d7791cc0 (base 9dbe8c83)

Scope (partial): new `check_array_map_coherence` (src/ast/array_map_coherence.h L1-198), its use in `array::solver::check_map_arrays` (src/sat/smt/array_axioms.cpp) and `theory_array_full::check_map_arrays` (src/smt/theory_array_full.cpp). Only the finite-domain coverage guard (L156-183) was examined. Excluded: definition-propagation/`collect` equality explanation, rewriter-based value comparison (L132-133, L148), the two wrappers' relevancy/justification plumbing, new tests, memory safety, termination, and C++ execution semantics.

## Obligations
1. **Proved** (abstract model, Bool domain): if store indices cover the whole domain, equal values at every store index imply array equality regardless of defaults (`covered_implies_equal`). This supports the `else` branch only when the indices truly cover the domain.
2. **Inconclusive**: the guard `domain_size > indices.size()` (L173) counts root-distinct index *nodes*, not distinct values. With Bool domain and two index nodes x1,x2 in different e-classes, count 2 >= 2 selects the select-only branch (L184-195) although a model may assign x1=x2, leaving the other domain value uncovered where defaults may differ. The F* module checks the abstract arrays (defaults 2 vs 3, indices [true;true]) agree on stores and differ outside, but this is NOT a reachable-witness proof: I did not establish that the solver can reach a final check with these e-classes unmerged and still return sat, nor that model construction/later checks do not re-detect it. Possible missed lemma -> incompleteness-of-check/soundness concern worth manual review (suggest a regression test with Bool-indexed arrays, two distinct index variables, const arrays with different defaults under map).
3. Not attempted (budget scope).

## Mapping and assumptions
F* `arr` models a const/map default plus store chain; `sel` is select. Domain size modeled as 2. No base F* modules imported beyond FStar.List.Tot. Assumptions: indices are arbitrary Bool terms; model-level equality of distinct roots is possible.

## Reproduce
See verification log; run from a fresh cache dir.