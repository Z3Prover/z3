# Audit of PR #11452 head c5d6464da39f60ae97b1e4cc040e34c61d27b14c
Delta audited: a2952e5..c5d6464. Source: src/opt/opt_nlsat.cpp lines 112-146 (sha256 of head file 1a5e44ec...3880f), fetched via contents API.
Change: bounded_limit_query becomes non-template, takes std::function(lbool()), and is exported in opt_nlsat.h; body unchanged. Plus a new unit test.
Obligations (all proved in F*, model Z3OptBoundedQuery.fst):
1. ticks==0 or already-canceled: query not called, l_undef, not rethrown.
2. Definite answer implies query ran and returned it normally.
3. External cancel at end of query is re-raised after pop (no swallowing); only a z3_exception without cancellation propagates.
Mapping: env abstracts cancel flag/message and exception kind; rlimit counting, verbose output are omitted.
Assumptions: m.inc() false iff cancel flag set; scoped_rlimit pop clears flag (per header comment/test); not verified from rlimit source.
Exclusions: std::function ABI/exception-safety, new test body, header include, earlier audited deltas, optsmt integration, memory safety.
Not mechanized C++ verification. Reproduce: /tmp/gh-aw/fstar/bin/fstar.exe --smt /tmp/gh-aw/fstar/lib/fstar/z3-4.13.3/bin/z3 --z3version 4.13.3 --z3rlimit 10 --cache_dir cache --odir out Z3OptBoundedQuery.fst