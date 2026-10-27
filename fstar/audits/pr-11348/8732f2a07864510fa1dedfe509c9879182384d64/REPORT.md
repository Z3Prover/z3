# F* audit PR #11348 @ 8732f2a07864510fa1dedfe509c9879182384d64 (base aa71a62fdffbfede37f7558b52da4d52841e04ea)

fstar-nfv-audit:8732f2a07864510fa1dedfe509c9879182384d64

## Scope
set_option_cmd::set_option, :global-declarations branch, src/cmd_context/basic_cmds.cpp (hunk @@ -523). This revision fixes the counterexample reported for 19d5ac8: set_global_decls is now called only inside the `if (global_decls != ctx.global_decls())` block, after check_not_initialized.

## Obligations (all proved)
1. o1: head never reaches set_global_decls with has_manager=true, so SASSERT(!has_manager()) (cmd_context.h:412) cannot fail.
2. o2: has_manager and changed value => throws (cmd_exception), same as base.
3. o3: on success option equals requested value; head differs from base only when has_manager, value unchanged, where it is a no-op instead of an error.

## Correspondence & assumptions
2-field abstraction (has_manager = m_manager != nullptr, global_decls = m_global_decls); check_not_initialized throws iff has_manager (basic_cmds.cpp:463). to_bool and parsing are not modelled. Manual source review only; not mechanized C++ semantics. Assumes ctx.global_decls() has no side effects (it is a plain getter, cmd_context.h:411). Inherits F* stdlib and Z3 4.13.3 trust.

## Excluded (not audited)
src/qe/qsat.cpp (fail_if_proof_generation moved earlier), src/smt/theory_arith_core.h, src/smt/theory_lra.cpp (assign -> mk_th_axiom under proofs; two sites), src/api/ml/CMakeLists.txt, all fstar/*.fst, fstar/cherry_runtime, fstar/ocaml_runtime, fstar/tools, and previous audit directories. Not reviewed for soundness: proof-mode th_axiom justification correctness and whether mk_th_axiom of a single literal is valid in those contexts.

## Reproduce
timeout 120 /tmp/gh-aw/fstar/bin/fstar.exe --smt /tmp/gh-aw/fstar/lib/fstar/z3-4.13.3/bin/z3 --z3version 4.13.3 --z3rlimit 10 --cache_dir cache --odir out GlobalDeclsFixedHead.fst
F* 2026.09.27, Z3 4.13.3.