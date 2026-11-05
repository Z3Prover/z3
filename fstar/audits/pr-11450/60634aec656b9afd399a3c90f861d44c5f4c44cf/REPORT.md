# F* audit, PR 11450 head 60634aec656b9afd399a3c90f861d44c5f4c44cf (base 1b859b6bc7637a9c802a92a0dee72df9e843274d)

Scope (partial): function `check_axiom` machinery in `src/sat/smt/arith_theory_checker.h` (head file sha256 da84304daec8d1d003583e7390a76f46f979cb598bf45975daa4c80e3cb321c2, 737 lines). The three audited functions are `is_infeasible` (~l.480-494), `expand_definitions` (~l.455-476), and `implies_nonnegative`/`is_abs_case` (~l.515-575). Earlier head e18979d was audited separately; this audit covers the C++ rule `arith` added after it.

## Obligations (all proved, mathematical model over integers)
- O1 is_infeasible: for any m in [0, |n|-1] (range of mod by nonzero numeral n), a row c*m+k that check_ineq accepts after the shift c<0 ? k+c*(|n|-1) : k is not <=0 (or <0 when strict). Proved.
- O2 expand_definitions: u = n*d + m implies c*m = c*u - (c*n)*d (mod rewrite), and n*q = u implies (c*q)*n = c*u (division by numeral, c/n scaling). Proved.
- O3 implies_nonnegative / abs case: if row r<=0 (or <0), lambda>0, and r + lambda*t is a constant >= 0 then t >= 0; and s*u >= 0 with s in {1,-1} gives abs u = s*u. Proved.

## Correspondence and assumptions
F* integers model rationals/integers of the C++ rational class; the row model abstracts the hash-map of coefficients to a single term. Assumed: Z3 semantics of div/mod (Euclidean, 0 <= mod < |n|), that `linearize`/`add` correctly compute linear forms (not mechanized), and that the negation encoding in add_literal is correct (reviewed manually, not proved). Integer-strictness tightening (m_coeff += coeff) is not modeled. The is_valid_literal equality branch and the clause() change in omitting `true` arguments (sound if the omitted literal is false at base level) are excluded and only manually reviewed. No counterexample was found, but this is not mechanized verification of C++ execution, memory safety, or the whole PR.

## Exclusions
All fstar/*.fst changes (Z3CoreKernel, Z3CoreModel, Z3BooleanRewrite, Z3BvWord, Z3ArithmeticRewrite etc.), src/test/proof_replay.cpp, proof_cmds.cpp, Python test, docs, and the remainder of arith_theory_checker.h are not audited.

## Reproduce
fstar.exe --smt /tmp/gh-aw/fstar/lib/fstar/z3-4.13.3/bin/z3 --z3version 4.13.3 --z3rlimit 10 --cache_dir cache --odir out AuditArithAxiom.fst
F* 2026.09.27; Z3 4.13.3 (pinned release backend). No admit/assume/lax.
