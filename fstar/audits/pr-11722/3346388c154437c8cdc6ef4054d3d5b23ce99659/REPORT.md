# F* audit PR 11722 @ 3346388c
Base f46b3c58. Sources (head blobs): src/opt/optsmt.cpp sha256 c4bafe313b43436903ff7cfbe6718d7615c8f3bfee281188e932d87471b3efd9 (geometric_opt ~107-175, update_lower ~739-750); src/opt/opt_solver.cpp sha256 1ae5e5473044cdf6b2c17996c1285e363a70967496b24a34d6513283bdd69bbe (lines 208-250); optsmt.cpp ~655-670 call site.

## Obligations
1. O1 (proved): in the new isolated scope (asserts base + assumptions, then rechecks), every surviving model satisfies the assumption literal b and base (b ==> x=0).
2. O2 (proved, refutation of OLD behaviour): witness {x=5,b=false} is admitted by old scope (max 5) but excluded by new scope (max 0). Not a counterexample to the PR.
3. O3 (proved): update_lower failure now yields l_undef and break instead of bound=true treated as sat.

## Correspondence
model (x,b) abstracts the PR test (b ==> x=0); filter models asserting m_assumptions and assumptions[]; unsat recheck => return false modeled as None. O3 models the bool return of update_lower.

## Assumptions
Solver check is an exact oracle on the finite candidate set; push/pop and LP state not modeled; maximize_objective returns true max. Inherited: FStar.List.Tot mem_filter. No admits/axioms.

## Not verified
C++ execution, memory safety, smt::context, exclusions listed in summary. An earlier audit of head 76f1ec30 exists; this is the new head.

## Reproduce
F* 2026.09.27, Z3 4.13.3.
timeout 120 /tmp/gh-aw/fstar/bin/fstar.exe --smt /tmp/gh-aw/fstar/lib/fstar/z3-4.13.3/bin/z3 --z3version 4.13.3 --z3rlimit 10 --cache_dir cache --odir out Pr11722Audit.fst
