## Scope
Head 7fbf34627ba3b2487f96cf604f2f08bb63842ab2, base aa71a62fdffbfede37f7558b52da4d52841e04ea. Source read via GitHub compare API patches; hunks only, not full functions, hashes not recorded. Tools: F* 2026.09.27, Z3 4.13.3 (pinned release backend).

## Obligations (all proved on the abstract model)
1. set_option_cmd global_decls (basic_cmds.cpp ~526): set_global_decls (SASSERT !has_manager) is only called when has_manager is false, so its precondition holds. PROVED (o1).
2. Behavior is identical to the old code, except that setting the same value after initialization is now accepted as a no-op. PROVED (o2).
3. An accepted set leaves global_decls equal to the requested value. PROVED (o3).
4. theory_arith_core.h / theory_lra.cpp (3 sites): the proof-mode dispatch is mk_th_axiom iff proofs are enabled, otherwise assign. PROVED (o4), on a trivial model.

## Not proved / assumptions
The model abstracts away: that mk_th_axiom produces a sound, checkable proof term for these literals (e.g. n/0 definitions and power0 underspecification); that ctx().assign without a justification is still safe in non-proof mode (unchanged behavior); the semantics of the qsat.cpp change (fail_if_proof_generation in qsat; simplify before qe_rec only under proofs); and the F* checker changes under fstar/ (Z3ArithmeticRewrite, Z3ArrayEquality, Z3SortedQuantifier, Z3BvFreshModel, Z3QuantifierReduce, etc.). These are excluded and unreviewed by this run. The earlier no-op set permits repeated (set-option :global-decls v) after init; this is a behavior relaxation and, per the model, safe for the SASSERT.

## Exclusions
qsat.cpp, src/api/ml and qe CMake files, src/test/smt_context.cpp, all fstar/** modules, OCaml runtime/tools, and prior audit directories.

## Correspondence
F* option/bool models mirror the guards one-to-one; no mechanized C++ execution, memory safety, or AST plumbing verification.

## Reproduce
fstar.exe --smt /tmp/gh-aw/fstar/lib/fstar/z3-4.13.3/bin/z3 --z3version 4.13.3 --z3rlimit 10 --cache_dir cache --odir out --include fstar Z3Pr11348Head7fbf.fst