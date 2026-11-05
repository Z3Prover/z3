## Scope
Base dd4179a5, head a6faede1, PR #11512 (open, no prior fstar-nfv-audit comment). Source: src/ast/simplifiers/finite_set_simplifier.cpp at head, sha256 of decoded file 410a748c2d4ccf6b22c183c635e3cc2468d46c586c3fa1c2ad35a1e47ea4abff, lines 212-224 (change at line 213: `if (m.is_eq(f))` -> `if (n == 2 && m.is_eq(f))`).

## Obligations (all proved)
1. O1: new guard implies reads of args[i], args[1-i] (i in {0,1}) are in bounds.
2. O2: for n=2 the new guard equals the old guard (behavior preserved on binary applications).
3. O3/O3b: the old guard admitted n=1 (reads args[1] OOB), the new guard rejects it. This witnesses the defect fixed, in the model; whether n!=2 equalities are reachable in practice is not established.

## Correspondence & assumptions
F* models only the guard predicate and index arithmetic; the filter/bounded rewrite branch is abstracted and not verified. Assumes n is the true length of args. Fall-through for n!=2 reaches the arithmetic/datatype normalization and BR_FAILED path, unchanged and not analyzed. No assumptions beyond F* stdlib and the pinned Z3 4.13.3; no base modules imported. Not verified: C++ execution, memory safety, AST plumbing.

## Exclusions (not audited, mostly non-solver)
.github/workflows/ci.yml, cmake/modules/FindDotnet.cmake, doc/mk_api_doc.py, src/api/java/{Context,Expr,FuncDecl,Global,IntNum,Model,OnClause,Optimize,Solver}.java (documentation), src/api/python/setup.py. The PR lists C# doc and .NET packaging changes; the file listing showed 11 of the 14 changed files plus others not individually inspected.

## Reproduce
/tmp/gh-aw/fstar/bin/fstar.exe --smt /tmp/gh-aw/fstar/lib/fstar/z3-4.13.3/bin/z3 --z3version 4.13.3 --z3rlimit 10 --cache_dir cache --odir out FiniteSetEqGuard.fst