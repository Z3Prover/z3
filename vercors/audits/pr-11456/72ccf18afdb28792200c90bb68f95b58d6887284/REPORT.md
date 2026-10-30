# VerCors C++ audit PR 11456 @ 72ccf18a

## Selected
Function: theory_finite_set::are_forced_distinct, src/smt/theory_finite_set.cpp L301-338 at head 72ccf18afdb28792200c90bb68f95b58d6887284 (SHA256 of decoded head file: 65e7a22f54693b4110b3f042aada52964be97bd2c5b3e542ea66aa4e30ed7a14).

- O1 (PROVED on extract): read permissions/array bounds, loop invariants, and postcondition: a true result implies one of (b empty and a has a true membership; a empty and b has a true membership; a common element root with differing defined values).
- O2 (non-vacuity, passes): ForcedDistinctWitness.cpp verifies a concrete state (a={7:true}, b={7:false}) satisfying the guard conditions. It is a separate unit and does not call the extract.
- O3: not attempted.

## Correspondence / abstractions (manual)
- enode parent iteration, ctx.is_relevant, u.is_in, get_root, find_assignment (lbool) are replaced by integer arrays: element root id and value 0=false, 1=true, 2=undef; filtering guards are modelled as pre-filtered inputs.
- The original obj_map (last write wins) is replaced by scanning all of a's entries; the postcondition shape (some conflicting pair exists) is therefore a modelling choice, not an exact match.
- is_empty (cyclic enode walk) is abstracted to booleans aEmpty/bEmpty; its termination is not checked.
- Array extents and read permissions are environment preconditions.
- Only int comparisons; no arithmetic overflow concerns.

## Semantic gaps
Not verified: that these facts truly imply set disequality (soundness of skipping the extensionality axiom), the finite_set_reuse_witness interaction, m_diseqs trail ordering, backtracking.

## Excluded
finite_set_simplifier.cpp, finite_set_tactic.cpp, theory_array_full.cpp instantiate_lambda_defaults, theory_finite_set add_setop/is_beta_redex changes, tests, python, params, F* audit files, CMake.

## Reproduce
In a clean directory with the .cpp file: /tmp/gh-aw/vercors/vercors --lang cpp --backend silicon --dev-total-timeout 60 $PWD/ForcedDistinct.cpp
