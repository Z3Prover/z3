# F* audit PR #11348 @ 19d5ac841ecbd2a5f0833ea5d41fb1dc6af727fa (base 9dbe8c83fcadaba50a607236894f72a63959a5da)

fstar-nfv-audit:19d5ac841ecbd2a5f0833ea5d41fb1dc6af727fa

## Scope
Audited: set_option_cmd::set_option, :global-declarations branch, src/cmd_context/basic_cmds.cpp (head blob 9d362f24b3537b65dc72061acebb44784bb0bacd, diff hunk @@ -523).

## Obligation 1: no assertion violation after change (COUNTEREXAMPLE)
Head: `bool g = to_bool(value); if (g != ctx.global_decls()) check_not_initialized(...); ctx.set_global_decls(g);`
cmd_context.h:412 `set_global_decls` has `SASSERT(!has_manager())`; has_manager() = m_manager != nullptr (cmd_context.h:433).
Witness: has_manager=true, global_decls=false (default), `(set-option :global-declarations false)` after the manager is initialized. The guard and throw are skipped and the SASSERT is violated; base code threw a cmd_exception. F* lemma cex() checks this in the model, and exact() characterises the violating inputs.
Impact: SASSERT is active only in debug builds; release builds just reassign the same value (benign). Debug builds abort on a user-reachable input. Fix: only call set_global_decls when the value changes, or relax the assertion.

## Correspondence & assumptions
2-field abstraction of the context; assumes SASSERT enabled. Manual source review, not mechanized C++ semantics. Whether the manager can be initialized before this command in practice was reviewed only by reading has_manager/init_manager usage.

## Excluded (not audited)
fstar/Z3IntegerDivision.fst, Z3SortedProof.fst, Z3SortedProofTests.fst, Z3SortedQuantifier.fst, tools/test_native_bridge.ml, tools/test_native_checker.py, OCAML_CHECKER_REPORT.md (F* proof edits are checked by their own verification, not audited here).

## Reproduce
timeout 120 /tmp/gh-aw/fstar/bin/fstar.exe --smt /tmp/gh-aw/fstar/lib/fstar/z3-4.13.3/bin/z3 --z3version 4.13.3 --z3rlimit 10 --cache_dir cache --odir out GlobalDeclsGuard.fst
F* 2026.09.27, Z3 4.13.3 (bundled).
