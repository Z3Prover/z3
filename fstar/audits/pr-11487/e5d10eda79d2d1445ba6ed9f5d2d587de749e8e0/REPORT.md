## Scope
PR #11487 head e5d10eda79d2d1445ba6ed9f5d2d587de749e8e0 (base deef01f5). Audited src/muz/spacer/spacer_global_generalizer.cpp lines 726-729 (mk_concretize_pob); head file sha256 692dd83c862d0578508d9073b41beb94b7414d70bb567672e534fd4085aae94a. Caller read: spacer_context.cpp ~3600-3619.

## Obligations (all proved)
- O1: null model => returns nullptr, no dereference.
- O2: original pob never modified on any path.
- O3: non-null model => behaviour identical to unguarded code.

## Correspondence
model_ref null <-> None; pob_concretizer::apply result abstracted as (proc_ok,newpost). The caller treats nullptr as a non-concretized path (falls through), so no new null handling is needed there.

## Assumptions
model_ref operator! tests the underlying pointer; apply is abstract; standard F* library only. Not mechanized: C++ execution, memory safety, pob_concretizer internals.

## Exclusions
src/test/spacer.cpp, src/test/main.cpp, src/test/CMakeLists.txt (tests); other get_model uses (e.g. line ~479) and the root cause of the null model from is_blocked (undef result) not audited.

## Reproduce
timeout 120 /tmp/gh-aw/fstar/bin/fstar.exe --smt /tmp/gh-aw/fstar/lib/fstar/z3-4.13.3/bin/z3 --z3version 4.13.3 --z3rlimit 10 --cache_dir cache --odir out ConcretizeNullGuard.fst

F* 2026.09.27, Z3 4.13.3.