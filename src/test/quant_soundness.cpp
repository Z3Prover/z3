/*++
Copyright (c) 2026 Microsoft Corporation

--*/

#include "api/z3.h"
#include "util/debug.h"

void tst_quant_soundness() {
    char const* benchmark = R"(
(declare-fun n (String String) Int)
(declare-const u String)
(assert (forall ((x String) (y String)) (or (= 0 (n y "")) (= 0 (str.len (str.++ (str.replace_re_all y (re.* (str.to_re y)) (str.from_int (n x y))) (str.from_code (str.to_code (str.at x (mod (abs (n y x)) (str.len x)))))))))))
(assert (= u (str.from_int (n u "."))))
)";
    Z3_config cfg = Z3_mk_config();
    Z3_context ctx = Z3_mk_context(cfg);
    Z3_del_config(cfg);
    Z3_ast_vector fmls = Z3_parse_smtlib2_string(ctx, benchmark, 0, nullptr, nullptr, 0, nullptr, nullptr);
    Z3_ast_vector_inc_ref(ctx, fmls);
    Z3_solver s = Z3_mk_solver(ctx);
    Z3_solver_inc_ref(ctx, s);
    for (unsigned i = 0; i < Z3_ast_vector_size(ctx, fmls); ++i)
        Z3_solver_assert(ctx, s, Z3_ast_vector_get(ctx, fmls, i));
    Z3_lbool r = Z3_solver_check(ctx, s);
    ENSURE(r == Z3_L_TRUE || r == Z3_L_UNDEF);
    Z3_solver_dec_ref(ctx, s);
    Z3_ast_vector_dec_ref(ctx, fmls);
    Z3_del_context(ctx);
}
