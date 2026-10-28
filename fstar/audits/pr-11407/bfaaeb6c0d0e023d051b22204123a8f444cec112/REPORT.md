# F* audit PR 11407 @ bfaaeb6c0d0e023d051b22204123a8f444cec112 (base 59e40ee67c582ca477c9e781a2d3388c91f726fa)

Partial semantic audit of an abstract guard model; not mechanized C++ verification (memory safety, AST plumbing, refcounts, exceptions not covered).

Sources (head, contents API): src/api/api_fpa.cpp sha256 bb6ee80b8feb2354bcbe3e1fd0343d6277f3a1e425720394ef361e0e7b60569b; src/api/api_algebraic.cpp sha256 8ce75cf0f2669cad9d6b02433d573fc203f03755cf82510a6ba3b1e06cd98a54. Both are byte-identical to the previously audited head 996486f7, so this audit re-verifies the same C++ on a new merge-from-master head. Base-file diff: only the hunks listed below.

## Obligations (3 groups; all proved)
1. G1 api_fpa.cpp:28-38 is_fp/is_rm/is_bv (`a != nullptr && is_expr(a) && pred(to_expr(a))`), used by Z3_mk_fpa_to_fp_float (~758), _bv (~794), _signed (~812): guard true implies Expr; Null and Sort never pass.
2. G2 api_algebraic.cpp:83-89 Z3_algebraic_is_value: CHECK_NON_NULL(a,false) (api_context.h:287) sets Z3_INVALID_ARG on null; non-null path never errors and true implies numeral/algebraic Expr.
3. G3 api_fpa.cpp ~776 Z3_mk_fpa_to_fp_real and ~1212 Z3_mk_fpa_to_fp_int_real: `!t || !is_expr(t) || ...` guards; acceptance implies all AST args are non-null Exprs. Plus a concrete Sort-as-expr rejection.
(Z3_fpa_is_numeral* guards at 1234-1332 were already present in the base for the cases checked and were not re-audited here.)

## Assumptions
is_expr(a) correctly discriminates expr from sort kind; predicate tags model fpa_util/arith_util/bv_util results on expressions; non-null pointers are valid live ASTs (ref-count validity, CHECK_VALID_AST, is not modelled); short-circuit || / && evaluation as in C++. Inherited: F* standard library and pinned Z3 4.13.3 SMT backend. No admit/assume/axioms.

## Exclusions
src/test/api_algebraic.cpp and src/test/fpa.cpp (tests); earlier PR commits' audit files under fstar/audits/pr-11407/996486f.... Remaining fp functions taking Z3_ast not changed by the PR (e.g. other mk_fpa_* with unchecked to_expr) are out of scope; the to_sort(s) guard `fu.is_float(to_sort(s))` still dereferences s without a null/is_sort check (unchanged, pre-existing, noted not proved).

## Reproduce
timeout 120 /tmp/gh-aw/fstar/bin/fstar.exe --smt /tmp/gh-aw/fstar/lib/fstar/z3-4.13.3/bin/z3 --z3version 4.13.3 --include fstar --z3rlimit 10 --cache_dir cache --odir out NullAstGuardsPr11407.fst
Result: exit 0, "All verification conditions discharged successfully". F* 2026.09.27, Z3 4.13.3.
