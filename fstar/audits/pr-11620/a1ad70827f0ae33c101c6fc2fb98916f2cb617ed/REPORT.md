# F* audit of PR #11620 @ a1ad70827f0ae33c101c6fc2fb98916f2cb617ed (base 532cbc4a)

Scope: PARTIAL. Not full PR coverage; not mechanized C++ verification.

Changed functions (<=3): (1) `evaluator_cfg::evaluate_partial_theory_func` (src/model/model_evaluator.cpp, removed `else if (!fi && is_considered_partially_interpreted ...)` branch, ~l.483 at base); (2) `arith_util::is_considered_partially_interpreted` (src/ast/arith_decl_plugin.cpp l.958-976, IDIV/MOD now use mk_idiv0()/mk_mod0()); (3) `arith_util::mk_idiv0/mk_mod0` (l.1034-1046, unchanged, used).
Source head hashes (sha256 of fetched files): arith_decl_plugin.cpp 873fc3bf97ab226d91f2570375ce98d13105d8252e9ae2dd7d6f5c8585456e85; model_evaluator.cpp a83d19394ea04f0307b69cb9ddc55b4210464cfcfc08ff1bd454d0fbbf2673cf.

## Obligations (module Pr11620Div.fst) - all PROVED
- O1: the removed rewrite `ite(0=y, f_ui(x,y), f(x,y))` is semantically equal to `f(x,y)` where f(x,y)=if y=0 then g else base. So removing it loses no semantics.
- O2: the removed rewrite's output contains the input redex f(x,y) as a strict subterm and is strictly larger. With BR_DONE this re-exposes the same redex: structural witness of the rewrite-growth/loop motivating the PR (abstract term model; not an execution trace of the C++ rewriter).
- O3: with the branch removed, ground evaluation of f(a,b) is still determined (zero divisor -> f_ui interpretation, via the unchanged is_considered_uninterpreted branch; else base).
- O4: refactor to mk_idiv0/mk_mod0 yields identical declaration keys (op, domain Int,Int, range Int) as the inlined code. Modelled as key equality; mk_func_decl hash-consing is assumed.

## Correspondence / assumptions
g,base are arbitrary total int functions (model interpretation of div0/mod0 and true division semantics); Num/App/G/IteZ abstract the C++ exprs. Assumes the rest of the rewriter evaluates f(x,y) once y becomes a numeral (not audited), mk_func_decl canonicalization, no F* assumes/admits; inherits F* standard library. No base proof modules imported.

## Not covered / manual review
REM branch (still maps to OP_MOD0 inline, pre-existing, unchanged; mk_rem0 also returns OP_MOD0); DIV real case (unchanged line); the 68-line unit test; other-theory callers of is_considered_partially_interpreted; memory/refcount; solver-wide effects. Existing audit comments on earlier heads not reused.

## Reproduce
F=/tmp/gh-aw/fstar; $F/bin/fstar.exe --smt $F/lib/fstar/z3-4.13.3/bin/z3 --z3version 4.13.3 --include fstar --z3rlimit 10 --cache_dir cache --odir out Pr11620Div.fst
