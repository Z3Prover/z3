## Scope
Changed function: `is_considered_partially_interpreted` in src/ast/arith_decl_plugin.cpp (head lines 967-973). Only change in PR; no exclusions beyond the rest of the file/solver.

## Source evidence
Head SHA f2ce8042347396272b57e6f1185cda36f1150dec, base f88557ef970a2997eae33a4a6644a6563fff49cb. head arith_decl_plugin.cpp sha256 49ee240dbc3b80eed6db794b1e90ad6211f30126360bfcb9918a02b3b2431433; arith_decl_plugin.h sha256 fe30ab494ab9060653d453579cb8aee50be6e0bc6142faf1f1a82fa7c144b56d. `arith_util::mk_rem0()` (cpp 1038-1041) is `rs={Int,Int}; mk_func_decl(arith_family_id, OP_MOD0, 0, nullptr, 2, rs, Int)`, textually identical to the removed inline code. Branch guard (`OP_REM`, n==2, `!is_numeral(args[1])`) is unchanged.

## Obligations (all proved)
1. `equiv`: old and new branch yield identical result under all guard inputs.
2. `same_as_mod0`: mk_rem0 declaration equals the OP_MOD0 declaration (also used by mk_mod0, is_rem0).
3. `sort_ok`: result op is MOD0 with domain (Int,Int), range Int.

## Correspondence and assumptions
F* models mk_func_decl as a deterministic constructor (assumption: manager hash-conses decls by family/op/params/sorts; memory, AST plumbing not modeled). Z3 manager state, ownership/ref counting of func_decl* not verified (same lifetime as before: manager-owned).

## Reproduce
`/tmp/gh-aw/fstar/bin/fstar.exe --smt /tmp/gh-aw/fstar/lib/fstar/z3-4.13.3/bin/z3 --z3version 4.13.3 --z3rlimit 10 --cache_dir cache --odir out Rem0Refactor.fst`. F* 2026.09.27, Z3 4.13.3. No admits/assumes.