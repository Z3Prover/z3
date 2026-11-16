F* 2026.09.27, Z3 4.13.3 (pinned independent backend). PR open at head 4a6e4ed6, base f46b3c58, no prior audit comment. Sources: optsmt.cpp head sha256 06e178df76bb025241959f6fce57a65662a9af878a6c41a5f2893352501b57df (lines 1020-1050), base sha256 746847ca8969d7926fa2d3f9c1c65fe00d0d5f6e9621eb861b44cf59bed6902d.

Change: in commit_assignment, when lo is finite and has zero infinitesimal and the objective is Int/Real, an additional plain arithmetic assertion obj >= (ceil(lo) for Int, lo for Real) is added after mk_ge.

Obligations (all PROVED in F*, module OptsmtCommitBound): O1 Int: x*d>=n iff x>=ceil(n/d) (added bound equivalent, no models lost); O2 ceil numeral is least integer >= lo; O3 Real: added bound is identical to the committed bound; O4 even for a strict Int bound the added bound is implied. Hence the added assertion is semantically implied by the committed bound: it cannot remove models or change optima; it only exposes the bound to arithmetic theory.

NOT established: that the fix resolves issue 11715 for all arith solvers/lex configurations, termination/performance effects, the unbounded-ness logic in other functions, rational::ceil implementation, mk_ge internals, memory safety. The F* module models value-level arithmetic only, not the C++ execution. Exclusions: src/test/opt_bounds.cpp (tests), other optsmt.cpp logic. Verdict is inconclusive because scope is partial and issue-level correctness was not proved, though no counterexample was found.

Assumptions: infinitesimal-zero guard modelled as exact rational bound; integers unbounded. No admit/assume.

Reproduce: timeout 120 /tmp/gh-aw/fstar/bin/fstar.exe --smt /tmp/gh-aw/fstar/lib/fstar/z3-4.13.3/bin/z3 --z3version 4.13.3 --z3rlimit 10 --cache_dir cache --odir out OptsmtCommitBound.fst