## Scope
Head 00f8831f81b3a879d4848502384d445949b94c17 (base 7fb2231271869cda03008f491526f2d57d079517), PR open, no prior audit comment. Audited ONLY the integer arithmetic functions `sum`, `product`, `subtract`, `calculate` in new fstar/Z3SortedInteger.fst (blob 1e7f36ff). This is a source-level semantic audit of the F* model, not verification of C++.
## Obligations (all proved)
1. `subtract (x::rest)` equals left-nested SMT-LIB `(- x r1 r2 ...)`; unary case is negation.
2. `sum`/`product` distribute over list append (n-ary flattening sound).
3. Concrete checks: subtract [1;2]=-1, [2;1]=1, [5]=-5 (Sub non-commutative, unary negation).
No counterexample found.
## Mapping/assumptions
My module re-states the PR functions on mathematical `int` (unbounded); the base modules (Z3AstTheory etc.) were NOT imported. Assumes Z3 integers are unbounded mathematical integers, as in the F* semantics; FStar.List.Tot and FStar.Math.Lemmas are standard-library trusted.
## Exclusions (not audited)
Z3SortedInteger: carrier/value/number/application/classify/lemma_* ; Z3SortedArithmetic.fst; Z3BooleanNormalForm, Z3DatatypeSignature, Z3DatatypeValue, Z3SortedDatatype, Z3SortedProof(+Tests), Z3SortedQuantifier, Z3SortedSemantics; OCAML_CHECKER_REPORT.md; fstar/tools/*. Also not covered: C++ execution, memory safety, whole solver, and the fidelity of the modelled functions to the PR text beyond manual reading.
## Versions
F* 2026.09.27; Z3 4.13.3 (pinned release backend).
## Reproduce
fstar.exe --smt /tmp/gh-aw/fstar/lib/fstar/z3-4.13.3/bin/z3 --z3version 4.13.3 --z3rlimit 10 --cache_dir cache --odir out Z3IntegerBridgeAudit.fst (timeout 120)