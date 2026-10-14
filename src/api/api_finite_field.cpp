/*++
Copyright (c) 2026 Romain Soulat

Module Name:

    api_finite_field.cpp

Abstract:

    C API for prime-field (finite field) sorts and values: sort creation from
    a decimal prime modulus, modulus accessors, and field arithmetic
    constructors (add, mul, neg, bitsum).

Author:

    Romain Soulat

--*/
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
    if (!prime || !*prime) {
        SET_ERROR_CODE(Z3_INVALID_ARG, "prime modulus must be a decimal integer");
        RETURN_Z3(nullptr);
    }
    rational p(prime);
    if (!p.is_int() || !p.is_pos()) {
        SET_ERROR_CODE(Z3_INVALID_ARG, "prime modulus must be a decimal integer");
        RETURN_Z3(nullptr);
    }
    sort *s = ff_util(mk_c(c)->m()).mk_sort(p);
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

MK_NARY(Z3_mk_ff_add, mk_c(c)->get_ff_fid(), OP_FF_ADD, SKIP);
MK_NARY(Z3_mk_ff_mul, mk_c(c)->get_ff_fid(), OP_FF_MUL, SKIP);
MK_NARY(Z3_mk_ff_bitsum, mk_c(c)->get_ff_fid(), OP_FF_BITSUM, SKIP);
MK_UNARY(Z3_mk_ff_neg, mk_c(c)->get_ff_fid(), OP_FF_NEG, SKIP);
}
