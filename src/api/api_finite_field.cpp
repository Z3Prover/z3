#include "api/z3.h"
#include "api/api_log_macros.h"
#include "api/api_context.h"
#include "api/api_util.h"
#include "ast/ff_decl_plugin.h"

extern "C" {
Z3_sort Z3_API Z3_mk_finite_field_sort(Z3_context c, Z3_string prime) {
    Z3_TRY;
    LOG_Z3_mk_finite_field_sort(c, prime);
    RESET_ERROR_CODE();
    if (!prime || !*prime || std::string(prime).find_first_not_of("0123456789") != std::string::npos) {
        SET_ERROR_CODE(Z3_INVALID_ARG, "prime modulus must be a decimal integer");
        RETURN_Z3(nullptr);
    }
    sort *s = ff_util(mk_c(c)->m()).mk_sort(rational(prime));
    mk_c(c)->save_ast_trail(s);
    RETURN_Z3(of_sort(s));
    Z3_CATCH_RETURN(nullptr);
}
Z3_string Z3_API Z3_get_finite_field_sort_size(Z3_context c, Z3_sort s) {
    Z3_TRY;
    LOG_Z3_get_finite_field_sort_size(c, s);
    RESET_ERROR_CODE();
    CHECK_VALID_AST(s, "");
    ff_util ff(mk_c(c)->m());
    if (!ff.is_ff(to_sort(s))) {
        SET_ERROR_CODE(Z3_INVALID_ARG, "finite-field sort expected");
        return "";
    }
    return mk_c(c)->mk_external_string(ff.modulus(to_sort(s)).to_string());
    Z3_CATCH_RETURN("");
}

Z3_ast Z3_API Z3_mk_ff_add(Z3_context c, unsigned n, Z3_ast const args[]) {
    Z3_TRY;
    LOG_Z3_mk_ff_add(c, n, args);
    RESET_ERROR_CODE();
    for (unsigned i = 0; i < n; ++i) {
        CHECK_IS_EXPR(args[i], nullptr);
    }
    app *a = ff_util(mk_c(c)->m()).mk_app(OP_FF_ADD, n, to_exprs(n, args));
    mk_c(c)->save_ast_trail(a);
    RETURN_Z3(of_ast(a));
    Z3_CATCH_RETURN(nullptr);
}

Z3_ast Z3_API Z3_mk_ff_mul(Z3_context c, unsigned n, Z3_ast const args[]) {
    Z3_TRY;
    LOG_Z3_mk_ff_mul(c, n, args);
    RESET_ERROR_CODE();
    for (unsigned i = 0; i < n; ++i) {
        CHECK_IS_EXPR(args[i], nullptr);
    }
    app *a = ff_util(mk_c(c)->m()).mk_app(OP_FF_MUL, n, to_exprs(n, args));
    mk_c(c)->save_ast_trail(a);
    RETURN_Z3(of_ast(a));
    Z3_CATCH_RETURN(nullptr);
}

Z3_ast Z3_API Z3_mk_ff_bitsum(Z3_context c, unsigned n, Z3_ast const args[]) {
    Z3_TRY;
    LOG_Z3_mk_ff_bitsum(c, n, args);
    RESET_ERROR_CODE();
    for (unsigned i = 0; i < n; ++i) {
        CHECK_IS_EXPR(args[i], nullptr);
    }
    app *a = ff_util(mk_c(c)->m()).mk_app(OP_FF_BITSUM, n, to_exprs(n, args));
    mk_c(c)->save_ast_trail(a);
    RETURN_Z3(of_ast(a));
    Z3_CATCH_RETURN(nullptr);
}

Z3_ast Z3_API Z3_mk_ff_neg(Z3_context c, Z3_ast a) {
    Z3_TRY;
    LOG_Z3_mk_ff_neg(c, a);
    RESET_ERROR_CODE();
    CHECK_IS_EXPR(a, nullptr);
    expr *arg = to_expr(a);
    app *r = ff_util(mk_c(c)->m()).mk_app(OP_FF_NEG, 1, &arg);
    mk_c(c)->save_ast_trail(r);
    RETURN_Z3(of_ast(r));
    Z3_CATCH_RETURN(nullptr);
}
}
