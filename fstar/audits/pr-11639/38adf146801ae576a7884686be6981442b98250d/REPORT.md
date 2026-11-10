# Audit PR 11639 @ 38adf146
Base 8927ff98. Changed: src/ast/rewriter/array_rewriter.cpp (mk_eq_core: removes const/lambda and lambda/lambda equality-to-forall rules, ~lines 881-905), src/test/simplifier.cpp, src/test/smt_context.cpp (tests only; excluded).

## Obligations (ArrayEqRemoval.fst)
- O1 PROVED: (= (const v) (lambda x. e)) <=> forall x. e=v under extensional array semantics (arrays as total functions).
- O2 PROVED: lambda/lambda equality with equal domain sorts <=> forall x. e1=e2.
- O3 PROVED (trivial): a non-firing rewrite preserves truth value.
Conclusion: deleting these rules cannot introduce unsoundness in this rewrite; it only drops completeness (the PR itself permits unknown for one case). Original issue #11556 (unsat reported as sat) is NOT shown fixed or not by this audit; the bug cause (e.g. quantifier handling elsewhere, var_shifter/de Bruijn, or MBQI) is not modeled.

## Assumptions
Extensional total-function array model; F* standard library. No admits/axioms.

## Exclusions
Tests in simplifier.cpp and smt_context.cpp; remaining mk_eq_core code; de Bruijn shifting correctness of removed code; solver behavior on #11556; C++ memory safety.

## Reproduce
fstar.exe (F* 2026.09.27) --smt /tmp/gh-aw/fstar/lib/fstar/z3-4.13.3/bin/z3 --z3version 4.13.3 --z3rlimit 10 --cache_dir cache --odir out ArrayEqRemoval.fst (exit 0). Z3 4.13.3.