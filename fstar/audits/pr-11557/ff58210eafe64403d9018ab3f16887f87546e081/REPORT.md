# Audit of PR #11557 at ff58210e (base 7b5c9fd6) - INCONCLUSIVE, partial scope

Changed: fstar/Z3RealPower.fst only (+4/-1): new lemma `negation_nonzero` (line 110) and its use in `reciprocal_at_zero_base` (line 302-307), replacing `assert (zero -. y =!= zero)`. This is one function plus a helper; no production C++ changed. Nothing else is covered.

Obligations
1. negation_nonzero: y != 0 => 0 - y != 0. PROVED in the standalone model (PR11557ZeroBase.fst).
2. reciprocal_at_zero_base head form: power 0 (-y) == inverse (power 0 y) for y != 0, using zero_base. PROVED in the model.
3. Whole real module Z3RealPower.fst verification under the pinned toolchain: INCONCLUSIVE. Both head and base fail (Error 19, timeout) at `negative_rational` (head line 213, base line 210) with --z3rlimit 10, before the PR's changed lemma is reached. So the claim that the module now verifies is not confirmed here; the PR's target lemma was not checked in its real context. This failure is a timeout, not a counterexample, and may reflect solver or flag differences from the repo's checker (strict flags not located in the trusted base).

Correspondence/assumptions: model mirrors the zero-base and y==0 branches of `power` and `inverse` with an abstract classifier; reals are FStar.Real (field axioms of F* standard library). The model does not include the real context, so it cannot show the earlier timeout was resolved. Note the old-form lemma also verifies in the model, so the model does not discriminate head from base. Mechanical proof of C++ execution, memory safety and the whole solver is not claimed.
Exclusions: all other lemmas in Z3RealPower.fst and dependent modules (Graphs, Certificates, Integer, Tests).
Reproduce: see verification log.
