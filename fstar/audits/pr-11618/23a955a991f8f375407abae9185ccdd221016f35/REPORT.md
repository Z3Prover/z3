# Partial audit of PR 11618 at 23a955a991f8f375407abae9185ccdd221016f35 (base 8573212f)

Scope: PR changes 29 files. Most changes are proof modules, tests, and prior audit bundles. This run audits ONE changed behavior: the new `concatMap` in `fstar/ocaml_runtime/fStar_List_Tot_Base.ml` (line 10, file sha256 03781b89e6cc0501946496f7612f83915a1a46bd00a3712e2645c9617f588101). It is a one-line addition, used by `Z3SortedRealDocumentTests.fst` line 352.

Intended property: the OCaml extraction stand-in `concatMap f l = Stdlib.List.concat_map f l` agrees with the F* spec `FStar.List.Tot.Base.concatMap` (in-order concatenation of `f` over `l`). Otherwise extracted checkers could diverge from the verified F* semantics.

Obligations (all **proved**):
1. `rev_app_spec`: the accumulator `rev_append` equals `rev l @ acc`.
2. `aux_correct`: the loop invariant `aux f acc l == rev acc @ concatMap f l`.
3. `concat_map_shim_correct`: `ocaml_concat_map f l == concatMap f l`.

F* to OCaml mapping: `ocaml_concat_map` models the OCaml stdlib accumulate-with-rev_append-then-reverse implementation of `List.concat_map`. Its use here is an assumption about the stdlib: not mechanically checked, and the OCaml version was not pinned. Pure-total `f` is assumed (extracted code may raise or diverge). Stack behavior on long lists is not modeled. No C++ is involved.

Assumptions inherited from the base: F* standard library lemmas (`append_assoc`, `rev_involutive`, `append_l_nil`) and the F* 2026.09.27 / Z3 4.13.3 toolchain. No admit, assume, or lax mode is used.

Excluded, not audited: the other 28 changed files. Those are Z3Sorted* proof/test changes (Z3CherryTests, Z3NnfReplay, Z3SortedProof, Z3SortedReal*, Z3SortedRoot*), build_ocaml_checker.ps1, checker_modules.json, the test_*.py/.ml checker tests, and the previous audit directories under fstar/audits/pr-11618. This is not full PR coverage.

Reproduce, from a directory containing AuditConcatMapShim.fst:
`/tmp/gh-aw/fstar/bin/fstar.exe --smt /tmp/gh-aw/fstar/lib/fstar/z3-4.13.3/bin/z3 --z3version 4.13.3 --z3rlimit 10 --cache_dir cache --odir out AuditConcatMapShim.fst`
