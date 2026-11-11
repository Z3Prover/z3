# F* audit: PR #11657 (head 1d12bbf8e97c81d907ff3f04299bbb98c62857fb, base 145c0c51570a357cc558ce898ce77573ba9d4fbf)

Scope is partial. Audited changed behaviour: `cmd_context::rollback_psort_decl` (new), and the rollback bookkeeping that `smt2parser.cpp` (`parse_declare_datatypes`, `parse_declare_datatype`, `parse_datatype_dec`, `parse_sort_decl_or_params`) drives through `new_sorts` + `on_scope_exit`. Source was read from the trusted base checkout for `cmd_context::insert` / `restore_psort_decls` and from the PR patch for new code; full PR-head function bodies were not fetched/hashed beyond the patch.

## Obligations (all on an abstract model, `Z3DtRollback.fst`)
Model: decls (m_psort_decls keys), stack (m_psort_decls_stack), global flag. `insert` mirrors `cmd_context::insert(symbol, psort_decl*)`: throws on an existing name, pushes to the stack only when `!m_global_decls`. `rollback` mirrors `erase_psort_decl_core` + conditional `pop_back`.
- O1 (proved): `run_shape` - after an insert sequence that may stop at the first failing (duplicate) insert, `new_sorts` holds exactly the newly inserted names, none pre-existing; scoped stack grew by exactly those; global stack unchanged.
- O2 (proved): `rollback_restores` - newest-first rollback restores the stack and removes exactly those names (so the SASSERT top==s holds on the modeled path).
- O3 (proved): `end_to_end` - insert-then-rollback leaves decls and stack equal to the pre-state, including duplicate names such as `((A 0) (A 0))` and names pre-existing (`Existing`), which are untouched. `dup_noop`: failed insert is a no-op.
No counterexample was sought-and-found; refutation attempt: the witness classes in the PR tests (duplicate, pre-existing, global/scoped) all satisfy the proved lemma.

## Assumptions
Names are modeled as nat; only name-registration bookkeeping is modeled. Assumes the parser inserts a sort at most once per new_sorts push, and that new_sorts.reset() occurs only after all sort-registering inserts. Base: F* standard library only (FStar.List.Tot, FStar.Classical); no admits/assumes.

## Not mechanized / excluded
- C++ execution, exceptions/unwinding ordering of `on_scope_exit`, ref-counting (`pm().dec_ref`) and potential dangling references from partially built pdatatype decls or `m_aux_pdecls`, memory safety.
- Non-2.6 path: `m_ctx.insert(d)` after `new_sorts.reset()` can still throw with partial insertion (not modeled).
- Moving `d->commit` after `check_rparen`, moving `check_duplicate` before commit, `parse_declare_datatype` flow, fix_missing_refs, and the regression test file (`src/test/parametric_datatype.cpp`) were reviewed by reading only.
- Interaction with `m_scopes` stack limits across push/pop is only covered by the stack-shape lemma, not by the real scope structure.
- cmd_context.h declaration change: trivial.

## Reproduce
`cd /tmp/gh-aw/agent/fstar-audit && timeout 120 /tmp/gh-aw/fstar/bin/fstar.exe --smt /tmp/gh-aw/fstar/lib/fstar/z3-4.13.3/bin/z3 --z3version 4.13.3 --include fstar --z3rlimit 10 --cache_dir cache --odir out Z3DtRollback.fst`
F* 2026.09.27; Z3 4.13.3 (pinned release backend).
