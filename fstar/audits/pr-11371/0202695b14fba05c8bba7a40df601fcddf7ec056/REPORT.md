# F* audit of PR 11371 (head 0202695b14fba05c8bba7a40df601fcddf7ec056, base 02f6a7e144ed5ce81ab07a1373fd667c60ead0c2)

Scope: PARTIAL. Only the semantic side conditions of C++ `arith_rewriter::factor_le_ge_eq` (src/ast/rewriter/arith_rewriter.cpp:729-762, trusted base) that the PR's `fstar/Z3ArithmeticFactor.fst` (head sha256 5aee0baf93...c9fab9, 504 lines) targets.

## Obligations (all proved)
1. p = f*g: (p = 0) <=> (f = 0 or g = 0)  [EQ branch], over reals.
2. GE branch: f*g >= 0 <=> ((f>=0) <=> (g>=0)) or f=0 or g=0, over reals and ints.
3. LE branch: f*g <= 0 <=> not((f>=0)<=>(g>=0)) or f=0 or g=0, over reals and ints.
No counterexample attempted succeeded; the identities hold, matching the C++ construction (mk_or / mk_iff / mk_not of mk_ge(f,0), mk_ge(f2,0)).

## Assumptions / correspondence
- C++ f2 = remove_factor(f, arg1) is assumed to satisfy arg1 = f*f2 (this is what the PR's ring-normalization check in `factorization` is meant to verify). NOT re-proved here.
- F* models values as FStar.Real / int with standard-library axioms; no admit/assume, no lax mode.
- This is a semantic model, not mechanized verification of C++ execution, AST plumbing, or memory safety.

## Exclusions (not audited)
Z3ArithmeticFactor.fst soundness lemmas (poly_of, atoms_of, lemma_check_sound, 4096 budget), Z3ArithmeticFactorTests.fst, Z3ConditionalRewrite.fst, Z3UnifiedProof.fst, OCaml checker tooling/tests and docs (OCAML_CHECKER_REPORT.md, PROOF_CHECKING.md, tools/*). PR proof modules were not imported or run. Whether the PR's checker accepts exactly the C++ outputs (e.g. find_nl_factor choice, remove_factor) is manually unreviewed.

## Reproduce
F=/tmp/gh-aw/fstar; $F/bin/fstar.exe --smt $F/lib/fstar/z3-4.13.3/bin/z3 --z3version 4.13.3 --z3rlimit 10 --cache_dir cache --odir out FactorSignAudit.fst
