# F* audit of PR 11450 at aebfac653c4d0da85e129c857fa02f90a6221f31 (base 9c7b1c6513ea0beb492f406dc7c29a85b175835e)

Partial scope. Selected changed functions in fstar/Z3BvWord.fst and fstar/Z3BvLemma.fst (new lemma_subtraction_words proof, lemma_concat_numeral_equality, lemma_add_number); each with one arithmetic obligation.

Obligations (all proved, AuditBvWord.fst):
- O1: (a-b) mod p == (a + ((p-1)*b mod p)) mod p, the bvsub = bvadd(a, bvmul(ones,b)) identity.
- O2: x*p+y == n <=> x == n/p /\ y == n mod p for x(pl, y<p (concat-vs-numeral equality splits into two conjuncts).
- O3: pa+pb == s + p*ov, s<p, ov in {0,1} implies (pa+pb) mod p == s (ripple-carry addition).

Correspondence: the F* modules are semantic models, not C++ execution. The audit models only the integer arithmetic of the repaired lemmas, not the full Z3 expr semantics. Assumptions: FStar.Math.Lemmas and the standard library only; no admits.

Excluded and not audited: all other changed fstar/*.fst modules (Z3StandardModel, Z3GhostStandardModel, Z3CoreKernel, Z3CoreModel, Z3AstTotEval, Z3BoundedBoolEquiv, Z3ResolutionProofTheory, etc.), src/sat/smt/arith_theory_checker.h, proof_cmds.cpp, Java/Maven, workflow and publishing scripts, tests, reports (arith checker audited earlier at 60634aec; canonical ops at e18979d6). Memory safety and C++ execution are not verified.

Reproduce: /tmp/gh-aw/fstar/bin/fstar.exe --smt /tmp/gh-aw/fstar/lib/fstar/z3-4.13.3/bin/z3 --z3version 4.13.3 --include /home/runner/work/z3/z3/fstar --z3rlimit 10 --cache_dir cache --odir out AuditBvWord.fst
