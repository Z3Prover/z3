# F* audit of PR #11211 delta 317d28d -> ced49cb (head ced49cb4a64c5d18319c5b94401ed37023cce062, base c1c2e52d)

Scope (partial, 3 changed functions): (1) algebraic_numbers::manager::to_rational (now returns bool, leaves r unchanged if irrational); (2) arith::solver::init_model (flag now taken from lp().init_model()); (3) get_power_value in sat/smt/arith_solver.cpp and theory_lra.cpp (SASSERT is_int, numerals returned unconditionally, NRA values need no LP init, irrational rejected, result must be integer).

Obligations (all PROVED in SwineAudit4.fst, exit 0, fresh cache):
- O1 irrational -> (false, r unchanged); basic -> (true, value).
- O2 flag true implies guard and lp().init_model() succeeded.
- O3 result is always an integer (given Int numerals are integers, matching the new SASSERT); irrational NRA -> none; LP value without init -> none; NRA rational integer needs no LP init.

Correspondence: small functional models of the C++ branches; not mechanized C++ execution, memory safety, scoped_mpq handling, trail/pop behavior, or lp().init_model internals (modelled as an opaque bool).
Assumptions: Int-sorted numerals are integers (SASSERT, checked only in debug builds); use_nra_model is a stable boolean.
Excluded (not audited): cmd_context builtin_decl m_func_decl/get_range refactor, arith_decl_plugin/ast.h changes, tests, theory_lra init_model beyond shared logic, SWiNE rewriter files, prior-audited earlier commits, docs.
Reproduce: fstar.exe --smt (pinned z3) --z3version 4.13.3 --include fstar --cache_dir cache --odir out --z3rlimit 10 SwineAudit4.fst
