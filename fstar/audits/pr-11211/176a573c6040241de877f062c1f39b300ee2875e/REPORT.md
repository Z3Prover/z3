## Scope
Head 176a573c6040241de877f062c1f39b300ee2875e, base c1c2e52d. Delta since last audited head e10c5f6f is the commit 176a573c (totalize real exponentiation). Source: src/ast/rewriter/arith_swine.cpp sha256 87dfed23...9d7eb (lines 12-57, 59-99, 111-156), fetched via contents API.

## Obligations (all proved)
- real_power_axioms: A1 scalar axioms (lines 23-38) never force incompatible value classes (zero/one/positive) given x=1 => x>0 and negative-base-undefined => exponent nonzero (even denominator or irrational). A2 root graph (lines 42-56): p^n = x^m with p>=0 for even n, and for odd n over all values, determines p uniquely (injectivity of n-th power).
- check_real_power: A3 weakened guard x<0 (lines 85-93) is sound given the axiom x<0 and even-denominator/irrational exponent => p=0.
- compute_power: B1 square-and-multiply loop (126-137) computes x^y. check_model: B2 early rejection (line 148) sound: |x|>=2, y>bits+1, |value|<2^bits => value != x^y.

## Correspondence and assumptions
Integers model the ordered field where only order/injectivity is needed; sign classes model the case analysis; B2 models bitsize as a bound |value|<2^bits (assumed property of rational::bitsize). Real-valued semantics of irrational exponent, AST plumbing, memory safety, resource limits (m.inc), the C++ execution, and the new shared validation in rewriter/theory_lra/arith_solver are not mechanized.

## Exclusions
arith_rewriter.cpp, purify_arith_tactic.cpp, theory_lra.cpp, sat/smt arith_solver/axioms/internalize, arith_decl_plugin, API/Python, tests, other fstar/Z3RealPower*.fst models, and arith_swine interpolation/monotonicity/prime/induction functions. These were not audited here (PR own F* modules not used as premises).

## Reproduce
fstar.exe --smt z3-4.13.3/bin/z3 --z3version 4.13.3 --include fstar --z3rlimit 10 --cache_dir cache --odir out SwineAudit6.fst. F* 2026.09.27, Z3 4.13.3. No admit/assume; only FStar.Math.Lemmas and Prims inherited.