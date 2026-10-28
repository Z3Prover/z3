# F* audit PR #11418 @ 68e81ec932d553a2ce85d0aa7dbebb26fd27ce1d (base 668d5979550e899e8341aad1b0a9ad6ff011f821)
Scope: PARTIAL. Semantic audit of the datatype subterm (⊑) logic in src/smt/theory_datatype.cpp (patch hunks read via the GitHub API; not full-function snapshots).
Selected functions: propagate_is_subterm, propagate_not_is_subterm, and the new subterm axiom in internalize_term_core (subterm predicate case).
## Obligations (all proved in Z3PR11418Subterm.fst)
1. O1 (propagate_is_subterm): clause ~(a⊑t) ∨ a=t ∨ a⊑arg_i... with the PR's positive polarity of recursive literals is valid for constructor t=Node l r. O1b: concrete witness (a=Leaf 0, t=Node (Leaf 0)(Leaf 0)) shows the OLD negated-recursive-literal polarity is unsound (clause false in a true model) — a bug fixed by the PR, not a counterexample to the PR. PROVED.
2. O2 (new antisymmetry axiom ~(a⊑b) ∨ ~(b⊑a) ∨ a=b): valid for finite trees via size-strictness. PROVED.
3. O3/O4 (propagate_not_is_subterm): reflexive ⊑ holds (so ~(a⊑a) conflict is right, premise now a=root eq); asserted units a≠t, ¬(a⊑l), ¬(a⊑r) follow from ¬(a⊑t). PROVED.
## Correspondence
F* tm models a binary-constructor datatype; sub is the inductive ⊑ (equality or subterm of some constructor arg). Clause literals map to the lits vectors in C++.
## Assumptions / not modeled
Environment: well-founded (finite) datatype values; congruence-closure e-graph guards (add_subterm_guards: n=root(n) equalities) are treated as true-in-model premises — the equality guards only weaken clauses so soundness reduces to the unguarded lemmas, but guard completeness (that all used equalities are included) is manually reviewed only. Multiple-constructor / non-recursive args modeled by one binary constructor.
## Excluded changes
smt2parser.cpp match-pattern constructor resolution; get_seq_args and sequence-cycle detection (occurs check / conflict explanations) incl. seq.nth cycles; add_subterm_predicate eager propagation and relevancy handling; theory_datatype.h; tests. Memory safety, e-graph mark handling (get_root()->set_mark), and C++ execution are not mechanized.
## Reproduce
See verification_log; base modules in fstar/ are not imported (self-contained).