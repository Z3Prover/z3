# F* audit of PR #11407 @ 996486f789e84edcd52feec86711ca607c5a9330 (base 668d5979550e899e8341aad1b0a9ad6ff011f821)

Partial, semantic source audit (not mechanized C++ verification).

Sources (head, via contents API): src/api/api_fpa.cpp sha256 bb6ee80b...0569b (1340 lines), src/api/api_algebraic.cpp sha256 8ce75cf0...8a54 (458 lines).

## Obligations (functions audited: is_fp/is_rm/is_bv helpers [api_fpa.cpp 28-38], Z3_algebraic_is_value(_core) [api_algebraic.cpp 74-90], Z3_fpa_is_numeral* [api_fpa.cpp ~1226-1340])
- O1 (proved): helpers return false for Null/sort ASTs and true only for expressions, so following to_expr() calls (mk_add, mk_fp, to_ubv, to_fp_float/signed/unsigned, ...) are reached only on real exprs.
- O2 (proved): Z3_algebraic_is_value(NULL) reports error and returns false; non-null never errors; true implies numeral/algebraic expr. The core guard also makes direct callers NULL-safe.
- O3 (proved): Z3_fpa_is_numeral* report error on NULL/non-expr/non-numeral and otherwise operate on an FP numeral expression.
- Refutation attempt: no counterexample found in the modelled guards.

## Correspondence / assumptions
The F* model abstracts an AST pointer as Null | SortAst | Expr with predicate tags; C++ short-circuit && / || is modelled as boolean ops. Assumed: to_expr is safe iff is_expr holds and pointer non-null; non-null pointers are valid live ASTs (is_expr itself dereferences; Z3_mk_fpa_* paths lack CHECK_VALID_AST, so dangling pointers remain out of scope). No admit/assume. Inherited: F* standard library only.

## Exclusions / manual review
Not modelled: Z3_mk_fpa_to_fp_real/int_real inline guards (same pattern, manually read: `!t || !is_expr(t) ||` precedes to_expr), error-code state (RESET_ERROR_CODE/SET_ERROR_CODE), to_sort(s) with s==NULL (unchanged, not guarded: Z3_mk_fpa_to_fp_* still call to_sort(s) unchecked -> NULL sort likely still crashes; observation, unproved), unchanged functions that call to_expr(t) after only is_fp-style checks, Z3_algebraic_* other functions (rely on core), tests (src/test/*.cpp, not audited), memory safety.

## Reproduce
fstar.exe --smt /tmp/gh-aw/fstar/lib/fstar/z3-4.13.3/bin/z3 --z3version 4.13.3 --include fstar --z3rlimit 10 --cache_dir cache --odir out NullAstGuards.fst
F* 2026.09.27 (commit 7deb38a2), Z3 4.13.3.
