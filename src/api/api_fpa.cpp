/*++
Copyright (c) 2013 Microsoft Corporation

Module Name:

    api_fpa.cpp

Abstract:

    Additional APIs for floating-point arithmetic (FP).

Author:

    Christoph M. Wintersteiger (cwinter) 2013-06-05

Notes:

--*/
#include<iostream>
#include "api/z3.h"
#include "api/api_log_macros.h"
#include "api/api_context.h"
#include "ast/fpa_decl_plugin.h"

static bool is_fp_sort(Z3_context c, Z3_sort s) {
    return mk_c(c)->fpautil().is_float(to_sort(s));
}

static bool is_fp(Z3_context c, Z3_ast a) {
    return mk_c(c)->fpautil().is_float(to_expr(a));
}

static bool is_rm(Z3_context c, Z3_ast a) {
    return mk_c(c)->fpautil().is_rm(to_expr(a));
}

static bool is_bv(Z3_context c, Z3_ast a) {
    return mk_c(c)->bvutil().is_bv(to_expr(a));
}

extern "C" {

    Z3_sort Z3_API Z3_mk_fpa_rounding_mode_sort(Z3_context c) {
        Z3_TRY;
        LOG_Z3_mk_fpa_rounding_mode_sort(c);
        RESET_ERROR_CODE();
        api::context * ctx = mk_c(c);
        sort * s = ctx->fpautil().mk_rm_sort();
        mk_c(c)->save_ast_trail(s);
        RETURN_Z3(of_sort(s));
        Z3_CATCH_RETURN(nullptr);
    }

    Z3_ast Z3_API Z3_mk_fpa_round_nearest_ties_to_even(Z3_context c) {
        Z3_TRY;
        LOG_Z3_mk_fpa_round_nearest_ties_to_even(c);
        RESET_ERROR_CODE();
        api::context * ctx = mk_c(c);
        expr * a = ctx->fpautil().mk_round_nearest_ties_to_even();
        ctx->save_ast_trail(a);
        RETURN_Z3(of_expr(a));
        Z3_CATCH_RETURN(nullptr);
    }

    Z3_ast Z3_API Z3_mk_fpa_rne(Z3_context c) {
        Z3_TRY;
        LOG_Z3_mk_fpa_rne(c);
        RESET_ERROR_CODE();
        api::context * ctx = mk_c(c);
        expr * a = ctx->fpautil().mk_round_nearest_ties_to_even();
        ctx->save_ast_trail(a);
        RETURN_Z3(of_expr(a));
        Z3_CATCH_RETURN(nullptr);
    }

    Z3_ast Z3_API Z3_mk_fpa_round_nearest_ties_to_away(Z3_context c) {
        Z3_TRY;
        LOG_Z3_mk_fpa_round_nearest_ties_to_away(c);
        RESET_ERROR_CODE();
        api::context * ctx = mk_c(c);
        expr * a = ctx->fpautil().mk_round_nearest_ties_to_away();
        ctx->save_ast_trail(a);
        RETURN_Z3(of_expr(a));
        Z3_CATCH_RETURN(nullptr);
    }

    Z3_ast Z3_API Z3_mk_fpa_rna(Z3_context c) {
        Z3_TRY;
        LOG_Z3_mk_fpa_rna(c);
        RESET_ERROR_CODE();
        api::context * ctx = mk_c(c);
        expr * a = ctx->fpautil().mk_round_nearest_ties_to_away();
        ctx->save_ast_trail(a);
        RETURN_Z3(of_expr(a));
        Z3_CATCH_RETURN(nullptr);
    }

    Z3_ast Z3_API Z3_mk_fpa_round_toward_positive(Z3_context c) {
        Z3_TRY;
        LOG_Z3_mk_fpa_round_toward_positive(c);
        RESET_ERROR_CODE();
        api::context * ctx = mk_c(c);
        expr * a = ctx->fpautil().mk_round_toward_positive();
        ctx->save_ast_trail(a);
        RETURN_Z3(of_expr(a));
        Z3_CATCH_RETURN(nullptr);
    }

    Z3_ast Z3_API Z3_mk_fpa_rtp(Z3_context c) {
        Z3_TRY;
        LOG_Z3_mk_fpa_rtp(c);
        RESET_ERROR_CODE();
        api::context * ctx = mk_c(c);
        expr * a = ctx->fpautil().mk_round_toward_positive();
        ctx->save_ast_trail(a);
        RETURN_Z3(of_expr(a));
        Z3_CATCH_RETURN(nullptr);
    }

    Z3_ast Z3_API Z3_mk_fpa_round_toward_negative(Z3_context c) {
        Z3_TRY;
        LOG_Z3_mk_fpa_round_toward_negative(c);
        RESET_ERROR_CODE();
        api::context * ctx = mk_c(c);
        expr * a = ctx->fpautil().mk_round_toward_negative();
        ctx->save_ast_trail(a);
        RETURN_Z3(of_expr(a));
        Z3_CATCH_RETURN(nullptr);
    }

    Z3_ast Z3_API Z3_mk_fpa_rtn(Z3_context c) {
        Z3_TRY;
        LOG_Z3_mk_fpa_rtn(c);
        RESET_ERROR_CODE();
        api::context * ctx = mk_c(c);
        expr * a = ctx->fpautil().mk_round_toward_negative();
        ctx->save_ast_trail(a);
        RETURN_Z3(of_expr(a));
        Z3_CATCH_RETURN(nullptr);
    }

    Z3_ast Z3_API Z3_mk_fpa_round_toward_zero(Z3_context c) {
        Z3_TRY;
        LOG_Z3_mk_fpa_round_toward_zero(c);
        RESET_ERROR_CODE();
        api::context * ctx = mk_c(c);
        expr * a = ctx->fpautil().mk_round_toward_zero();
        ctx->save_ast_trail(a);
        RETURN_Z3(of_expr(a));
        Z3_CATCH_RETURN(nullptr);
    }

    Z3_ast Z3_API Z3_mk_fpa_rtz(Z3_context c) {
        Z3_TRY;
        LOG_Z3_mk_fpa_rtz(c);
        RESET_ERROR_CODE();
        api::context * ctx = mk_c(c);
        expr * a = ctx->fpautil().mk_round_toward_zero();
        ctx->save_ast_trail(a);
        RETURN_Z3(of_expr(a));
        Z3_CATCH_RETURN(nullptr);
    }


    Z3_sort Z3_API Z3_mk_fpa_sort(Z3_context c, unsigned ebits, unsigned sbits) {
        Z3_TRY;
        LOG_Z3_mk_fpa_sort(c, ebits, sbits);
        RESET_ERROR_CODE();
        if (ebits < 2 || sbits < 3) {
            SET_ERROR_CODE(Z3_INVALID_ARG, "ebits should be at least 2, sbits at least 3");
        }
        api::context * ctx = mk_c(c);
        sort * s = ctx->fpautil().mk_float_sort(ebits, sbits);
        ctx->save_ast_trail(s);
        RETURN_Z3(of_sort(s));
        Z3_CATCH_RETURN(nullptr);
    }

    Z3_sort Z3_API Z3_mk_fpa_sort_half(Z3_context c) {
        return Z3_mk_fpa_sort(c, 5, 11);
    }

    Z3_sort Z3_API Z3_mk_fpa_sort_16(Z3_context c) {
        return Z3_mk_fpa_sort(c, 5, 11);
    }

    Z3_sort Z3_API Z3_mk_fpa_sort_single(Z3_context c) {
        return Z3_mk_fpa_sort(c, 8, 24);
    }

    Z3_sort Z3_API Z3_mk_fpa_sort_32(Z3_context c) {
        return Z3_mk_fpa_sort(c, 8, 24);
    }

    Z3_sort Z3_API Z3_mk_fpa_sort_double(Z3_context c) {
        return Z3_mk_fpa_sort(c, 11, 53);
    }

    Z3_sort Z3_API Z3_mk_fpa_sort_64(Z3_context c) {
        return Z3_mk_fpa_sort(c, 11, 53);
    }

    Z3_sort Z3_API Z3_mk_fpa_sort_quadruple(Z3_context c) {
        return Z3_mk_fpa_sort(c, 15, 113);
    }

    Z3_sort Z3_API Z3_mk_fpa_sort_128(Z3_context c) {
        return Z3_mk_fpa_sort(c, 15, 113);
    }

    Z3_ast Z3_API Z3_mk_fpa_nan(Z3_context c, Z3_sort s) {
        Z3_TRY;
        LOG_Z3_mk_fpa_nan(c, s);
        RESET_ERROR_CODE();
        CHECK_VALID_AST(s, nullptr);
        if (!is_fp_sort(c, s)) {
            SET_ERROR_CODE(Z3_INVALID_ARG, "fp sort expected");
            RETURN_Z3(nullptr);
        }
        api::context * ctx = mk_c(c);
        expr * a = ctx->fpautil().mk_nan(to_sort(s));
        ctx->save_ast_trail(a);
        RETURN_Z3(of_expr(a));
        Z3_CATCH_RETURN(nullptr);
    }

    Z3_ast Z3_API Z3_mk_fpa_inf(Z3_context c, Z3_sort s, bool negative) {
        Z3_TRY;
        LOG_Z3_mk_fpa_inf(c, s, negative);
        RESET_ERROR_CODE();
        CHECK_VALID_AST(s, nullptr);
        if (!is_fp_sort(c, s)) {
            SET_ERROR_CODE(Z3_INVALID_ARG, "fp sort expected");
            RETURN_Z3(nullptr);
        }
        api::context * ctx = mk_c(c);
        expr * a = negative ? ctx->fpautil().mk_ninf(to_sort(s)) :
                              ctx->fpautil().mk_pinf(to_sort(s));
        ctx->save_ast_trail(a);
        RETURN_Z3(of_expr(a));
        Z3_CATCH_RETURN(nullptr);
    }

    Z3_ast Z3_API Z3_mk_fpa_zero(Z3_context c, Z3_sort s, bool negative) {
        Z3_TRY;
        LOG_Z3_mk_fpa_inf(c, s, negative);
        RESET_ERROR_CODE();
        CHECK_VALID_AST(s, nullptr);
        if (!is_fp_sort(c, s)) {
            SET_ERROR_CODE(Z3_INVALID_ARG, "fp sort expected");
            RETURN_Z3(nullptr);
        }
        api::context * ctx = mk_c(c);
        expr * a = negative ? ctx->fpautil().mk_nzero(to_sort(s)) :
                              ctx->fpautil().mk_pzero(to_sort(s));
        ctx->save_ast_trail(a);
        RETURN_Z3(of_expr(a));
        Z3_CATCH_RETURN(nullptr);
    }

    Z3_ast Z3_API Z3_mk_fpa_fp(Z3_context c, Z3_ast sgn, Z3_ast exp, Z3_ast sig) {
        Z3_TRY;
        LOG_Z3_mk_fpa_fp(c, sgn, exp, sig);
        RESET_ERROR_CODE();
        if (!is_bv(c, sgn) || !is_bv(c, exp) || !is_bv(c, sig)) {
            SET_ERROR_CODE(Z3_INVALID_ARG, "bv sorts expected for arguments");
            RETURN_Z3(nullptr);
        }
        api::context * ctx = mk_c(c);
        expr * a = ctx->fpautil().mk_fp(to_expr(sgn), to_expr(exp), to_expr(sig));
        ctx->save_ast_trail(a);
        RETURN_Z3(of_expr(a));
        Z3_CATCH_RETURN(nullptr);
    }

    Z3_ast Z3_API Z3_mk_fpa_numeral_float(Z3_context c, float v, Z3_sort ty) {
        Z3_TRY;
        LOG_Z3_mk_fpa_numeral_float(c, v, ty);
        RESET_ERROR_CODE();
        if (!is_fp_sort(c, ty)) {
            SET_ERROR_CODE(Z3_INVALID_ARG,"fp sort expected");
            RETURN_Z3(nullptr);
        }
        api::context * ctx = mk_c(c);
        scoped_mpf tmp(ctx->fpautil().fm());
        ctx->fpautil().fm().set(tmp,
                                ctx->fpautil().get_ebits(to_sort(ty)),
                                ctx->fpautil().get_sbits(to_sort(ty)),
                                v);
        expr * a = ctx->fpautil().mk_value(tmp);
        ctx->save_ast_trail(a);
        RETURN_Z3(of_expr(a));
        Z3_CATCH_RETURN(nullptr);
    }

    Z3_ast Z3_API Z3_mk_fpa_numeral_double(Z3_context c, double v, Z3_sort ty) {
        Z3_TRY;
        LOG_Z3_mk_fpa_numeral_double(c, v, ty);
        RESET_ERROR_CODE();
        if (!is_fp_sort(c, ty)) {
            SET_ERROR_CODE(Z3_INVALID_ARG, "fp sort expected");
            RETURN_Z3(nullptr);
        }
        api::context * ctx = mk_c(c);
        scoped_mpf tmp(ctx->fpautil().fm());
        ctx->fpautil().fm().set(tmp, ctx->fpautil().get_ebits(to_sort(ty)), ctx->fpautil().get_sbits(to_sort(ty)), v);
        expr * a = ctx->fpautil().mk_value(tmp);
        ctx->save_ast_trail(a);
        RETURN_Z3(of_expr(a));
        Z3_CATCH_RETURN(nullptr);
    }

    Z3_ast Z3_API Z3_mk_fpa_numeral_int(Z3_context c, signed v, Z3_sort ty) {
        Z3_TRY;
        LOG_Z3_mk_fpa_numeral_int(c, v, ty);
        RESET_ERROR_CODE();
        if (!is_fp_sort(c, ty)) {
            SET_ERROR_CODE(Z3_INVALID_ARG, "fp sort expected");
            RETURN_Z3(nullptr);
        }
        api::context * ctx = mk_c(c);
        scoped_mpf tmp(ctx->fpautil().fm());
        ctx->fpautil().fm().set(tmp,
                                ctx->fpautil().get_ebits(to_sort(ty)),
                                ctx->fpautil().get_sbits(to_sort(ty)),
                                v);
        expr * a = ctx->fpautil().mk_value(tmp);
        ctx->save_ast_trail(a);
        RETURN_Z3(of_expr(a));
        Z3_CATCH_RETURN(nullptr);
    }

    Z3_ast Z3_API Z3_mk_fpa_numeral_int_uint(Z3_context c, bool sgn, signed exp, unsigned sig, Z3_sort ty) {
        Z3_TRY;
        LOG_Z3_mk_fpa_numeral_int64_uint64(c, sgn, exp, sig, ty);
        RESET_ERROR_CODE();
        if (!is_fp_sort(c, ty)) {
            SET_ERROR_CODE(Z3_INVALID_ARG, "fp sort expected");
            RETURN_Z3(nullptr);
        }
        api::context * ctx = mk_c(c);
        scoped_mpf tmp(ctx->fpautil().fm());
        ctx->fpautil().fm().set(tmp,
                                ctx->fpautil().get_ebits(to_sort(ty)),
                                ctx->fpautil().get_sbits(to_sort(ty)),
                                sgn, exp, sig);
        expr * a = ctx->fpautil().mk_value(tmp);
        ctx->save_ast_trail(a);
        RETURN_Z3(of_expr(a));
        Z3_CATCH_RETURN(nullptr);
    }

    Z3_ast Z3_API Z3_mk_fpa_numeral_int64_uint64(Z3_context c, bool sgn, int64_t exp, uint64_t sig, Z3_sort ty) {
        Z3_TRY;
        LOG_Z3_mk_fpa_numeral_int64_uint64(c, sgn, exp, sig, ty);
        RESET_ERROR_CODE();
        if (!is_fp_sort(c, ty)) {
            SET_ERROR_CODE(Z3_INVALID_ARG, "fp sort expected");
            RETURN_Z3(nullptr);
        }
        api::context * ctx = mk_c(c);
        scoped_mpf tmp(ctx->fpautil().fm());
        ctx->fpautil().fm().set(tmp,
                                ctx->fpautil().get_ebits(to_sort(ty)),
                                ctx->fpautil().get_sbits(to_sort(ty)),
                                sgn, exp, sig);
        expr * a = ctx->fpautil().mk_value(tmp);
        ctx->save_ast_trail(a);
        RETURN_Z3(of_expr(a));
        Z3_CATCH_RETURN(nullptr);
    }

    Z3_ast Z3_API Z3_mk_fpa_abs(Z3_context c, Z3_ast t) {
        Z3_TRY;
        LOG_Z3_mk_fpa_abs(c, t);
        RESET_ERROR_CODE();
        if (!is_fp(c, t)) {
            SET_ERROR_CODE(Z3_INVALID_ARG, "fp sort expected");
            RETURN_Z3(nullptr);
        }
        api::context * ctx = mk_c(c);
        expr * a = ctx->fpautil().mk_abs(to_expr(t));
        ctx->save_ast_trail(a);
        RETURN_Z3(of_expr(a));
        Z3_CATCH_RETURN(nullptr);
    }

    Z3_ast Z3_API Z3_mk_fpa_neg(Z3_context c, Z3_ast t) {
        Z3_TRY;
        LOG_Z3_mk_fpa_neg(c, t);
        RESET_ERROR_CODE();
        if (!is_fp(c, t)) {
            SET_ERROR_CODE(Z3_INVALID_ARG, "fp sort expected");
            RETURN_Z3(nullptr);
        }
        api::context * ctx = mk_c(c);
        expr * a = ctx->fpautil().mk_neg(to_expr(t));
        ctx->save_ast_trail(a);
        RETURN_Z3(of_expr(a));
        Z3_CATCH_RETURN(nullptr);
    }

    Z3_ast Z3_API Z3_mk_fpa_add(Z3_context c, Z3_ast rm, Z3_ast t1, Z3_ast t2) {
        Z3_TRY;
        LOG_Z3_mk_fpa_add(c, rm, t1, t2);
        RESET_ERROR_CODE();
        if (!is_rm(c, rm) || !is_fp(c, t1) || !is_fp(c, t2)) {
            SET_ERROR_CODE(Z3_INVALID_ARG, "rm and fp sorts expected");
            RETURN_Z3(nullptr);
        }
        api::context * ctx = mk_c(c);
        expr * a = ctx->fpautil().mk_add(to_expr(rm), to_expr(t1), to_expr(t2));
        ctx->save_ast_trail(a);
        RETURN_Z3(of_expr(a));
        Z3_CATCH_RETURN(nullptr);
    }

    Z3_ast Z3_API Z3_mk_fpa_sub(Z3_context c, Z3_ast rm, Z3_ast t1, Z3_ast t2) {
        Z3_TRY;
        LOG_Z3_mk_fpa_add(c, rm, t1, t2);
        RESET_ERROR_CODE();
        if (!is_rm(c, rm) || !is_fp(c, t1) || !is_fp(c, t2)) {
            SET_ERROR_CODE(Z3_INVALID_ARG, "rm and fp sorts expected");
            RETURN_Z3(nullptr);
        }
        api::context * ctx = mk_c(c);
        expr * a = ctx->fpautil().mk_sub(to_expr(rm), to_expr(t1), to_expr(t2));
        ctx->save_ast_trail(a);
        RETURN_Z3(of_expr(a));
        Z3_CATCH_RETURN(nullptr);
    }

    Z3_ast Z3_API Z3_mk_fpa_mul(Z3_context c, Z3_ast rm, Z3_ast t1, Z3_ast t2) {
        Z3_TRY;
        LOG_Z3_mk_fpa_add(c, rm, t1, t2);
        RESET_ERROR_CODE();
        if (!is_rm(c, rm) || !is_fp(c, t1) || !is_fp(c, t2)) {
            SET_ERROR_CODE(Z3_INVALID_ARG, "rm and fp sorts expected");
            RETURN_Z3(nullptr);
        }
        api::context * ctx = mk_c(c);
        expr * a = ctx->fpautil().mk_mul(to_expr(rm), to_expr(t1), to_expr(t2));
        ctx->save_ast_trail(a);
        RETURN_Z3(of_expr(a));
        Z3_CATCH_RETURN(nullptr);
    }

    Z3_ast Z3_API Z3_mk_fpa_div(Z3_context c, Z3_ast rm, Z3_ast t1, Z3_ast t2) {
        Z3_TRY;
        LOG_Z3_mk_fpa_add(c, rm, t1, t2);
        RESET_ERROR_CODE();
        if (!is_rm(c, rm) || !is_fp(c, t1) || !is_fp(c, t2)) {
            SET_ERROR_CODE(Z3_INVALID_ARG, "rm and fp sorts expected");
            RETURN_Z3(nullptr);
        }
        api::context * ctx = mk_c(c);
        expr * a = ctx->fpautil().mk_div(to_expr(rm), to_expr(t1), to_expr(t2));
        ctx->save_ast_trail(a);
        RETURN_Z3(of_expr(a));
        Z3_CATCH_RETURN(nullptr);
    }

    Z3_ast Z3_API Z3_mk_fpa_fma(Z3_context c, Z3_ast rm, Z3_ast t1, Z3_ast t2, Z3_ast t3) {
        Z3_TRY;
        LOG_Z3_mk_fpa_fma(c, rm, t1, t2, t3);
        RESET_ERROR_CODE();
        if (!is_rm(c, rm) || !is_fp(c, t1) || !is_fp(c, t2) || !is_fp(c, t3)) {
            SET_ERROR_CODE(Z3_INVALID_ARG, "rm and fp sorts expected");
            RETURN_Z3(nullptr);
        }
        api::context * ctx = mk_c(c);
        expr * a = ctx->fpautil().mk_fma(to_expr(rm), to_expr(t1), to_expr(t2), to_expr(t3));
        ctx->save_ast_trail(a);
        RETURN_Z3(of_expr(a));
        Z3_CATCH_RETURN(nullptr);
    }

    Z3_ast Z3_API Z3_mk_fpa_sqrt(Z3_context c, Z3_ast rm, Z3_ast t) {
        Z3_TRY;
        LOG_Z3_mk_fpa_sqrt(c, rm, t);
        RESET_ERROR_CODE();
        if (!is_rm(c, rm) || !is_fp(c, t)) {
            SET_ERROR_CODE(Z3_INVALID_ARG, "rm and fp sorts expected");
            RETURN_Z3(nullptr);
        }
        api::context * ctx = mk_c(c);
        expr * a = ctx->fpautil().mk_sqrt(to_expr(rm), to_expr(t));
        ctx->save_ast_trail(a);
        RETURN_Z3(of_expr(a));
        Z3_CATCH_RETURN(nullptr);
    }

    Z3_ast Z3_API Z3_mk_fpa_rem(Z3_context c, Z3_ast t1, Z3_ast t2) {
        Z3_TRY;
        LOG_Z3_mk_fpa_rem(c, t1, t2);
        RESET_ERROR_CODE();
        if (!is_fp(c, t1) || !is_fp(c, t2)) {
            SET_ERROR_CODE(Z3_INVALID_ARG, "fp sorts expected");
            RETURN_Z3(nullptr);
        }
        api::context * ctx = mk_c(c);
        expr * a = ctx->fpautil().mk_rem(to_expr(t1), to_expr(t2));
        ctx->save_ast_trail(a);
        RETURN_Z3(of_expr(a));
        Z3_CATCH_RETURN(nullptr);
    }

    Z3_ast Z3_API Z3_mk_fpa_round_to_integral(Z3_context c, Z3_ast rm, Z3_ast t) {
        Z3_TRY;
        LOG_Z3_mk_fpa_round_to_integral(c, rm, t);
        RESET_ERROR_CODE();
        if (!is_rm(c, rm) || !is_fp(c, t)) {
            SET_ERROR_CODE(Z3_INVALID_ARG, "rm and fp sorts expected");
            RETURN_Z3(nullptr);
        }
        api::context * ctx = mk_c(c);
        expr * a = ctx->fpautil().mk_round_to_integral(to_expr(rm), to_expr(t));
        ctx->save_ast_trail(a);
        RETURN_Z3(of_expr(a));
        Z3_CATCH_RETURN(nullptr);
    }

    Z3_ast Z3_API Z3_mk_fpa_min(Z3_context c, Z3_ast t1, Z3_ast t2) {
        Z3_TRY;
        LOG_Z3_mk_fpa_min(c, t1, t2);
        RESET_ERROR_CODE();
        if (!is_fp(c, t1) || !is_fp(c, t2)) {
            SET_ERROR_CODE(Z3_INVALID_ARG, "fp sorts expected");
            RETURN_Z3(nullptr);
        }
        api::context * ctx = mk_c(c);
        expr * a = ctx->fpautil().mk_min(to_expr(t1), to_expr(t2));
        ctx->save_ast_trail(a);
        RETURN_Z3(of_expr(a));
        Z3_CATCH_RETURN(nullptr);
    }

    Z3_ast Z3_API Z3_mk_fpa_max(Z3_context c, Z3_ast t1, Z3_ast t2) {
        Z3_TRY;
        LOG_Z3_mk_fpa_max(c, t1, t2);
        RESET_ERROR_CODE();
        if (!is_fp(c, t1) || !is_fp(c, t2)) {
            SET_ERROR_CODE(Z3_INVALID_ARG, "fp sorts expected");
            RETURN_Z3(nullptr);
        }
        api::context * ctx = mk_c(c);
        expr * a = ctx->fpautil().mk_max(to_expr(t1), to_expr(t2));
        ctx->save_ast_trail(a);
        RETURN_Z3(of_expr(a));
        Z3_CATCH_RETURN(nullptr);
    }

    Z3_ast Z3_API Z3_mk_fpa_leq(Z3_context c, Z3_ast t1, Z3_ast t2) {
        Z3_TRY;
        LOG_Z3_mk_fpa_leq(c, t1, t2);
        RESET_ERROR_CODE();
        if (!is_fp(c, t1) || !is_fp(c, t2)) {
            SET_ERROR_CODE(Z3_INVALID_ARG, "fp sorts expected");
            RETURN_Z3(nullptr);
        }
        api::context * ctx = mk_c(c);
        expr * a = ctx->fpautil().mk_le(to_expr(t1), to_expr(t2));
        ctx->save_ast_trail(a);
        RETURN_Z3(of_expr(a));
        Z3_CATCH_RETURN(nullptr);
    }

    Z3_ast Z3_API Z3_mk_fpa_lt(Z3_context c, Z3_ast t1, Z3_ast t2) {
        Z3_TRY;
        LOG_Z3_mk_fpa_lt(c, t1, t2);
        RESET_ERROR_CODE();
        if (!is_fp(c, t1) || !is_fp(c, t2)) {
            SET_ERROR_CODE(Z3_INVALID_ARG, "fp sorts expected");
            RETURN_Z3(nullptr);
        }
        api::context * ctx = mk_c(c);
        expr * a = ctx->fpautil().mk_lt(to_expr(t1), to_expr(t2));
        ctx->save_ast_trail(a);
        RETURN_Z3(of_expr(a));
        Z3_CATCH_RETURN(nullptr);
    }

    Z3_ast Z3_API Z3_mk_fpa_geq(Z3_context c, Z3_ast t1, Z3_ast t2) {
        Z3_TRY;
        LOG_Z3_mk_fpa_geq(c, t1, t2);
        RESET_ERROR_CODE();
        if (!is_fp(c, t1) || !is_fp(c, t2)) {
            SET_ERROR_CODE(Z3_INVALID_ARG, "fp sorts expected");
            RETURN_Z3(nullptr);
        }
        api::context * ctx = mk_c(c);
        expr * a = ctx->fpautil().mk_ge(to_expr(t1), to_expr(t2));
        ctx->save_ast_trail(a);
        RETURN_Z3(of_expr(a));
        Z3_CATCH_RETURN(nullptr);
    }

    Z3_ast Z3_API Z3_mk_fpa_gt(Z3_context c, Z3_ast t1, Z3_ast t2) {
        Z3_TRY;
        LOG_Z3_mk_fpa_gt(c, t1, t2);
        RESET_ERROR_CODE();
        if (!is_fp(c, t1) || !is_fp(c, t2)) {
            SET_ERROR_CODE(Z3_INVALID_ARG, "fp sorts expected");
            RETURN_Z3(nullptr);
        }
        api::context * ctx = mk_c(c);
        expr * a = ctx->fpautil().mk_gt(to_expr(t1), to_expr(t2));
        ctx->save_ast_trail(a);
        RETURN_Z3(of_expr(a));
        Z3_CATCH_RETURN(nullptr);
    }

    Z3_ast Z3_API Z3_mk_fpa_eq(Z3_context c, Z3_ast t1, Z3_ast t2) {
        Z3_TRY;
        LOG_Z3_mk_fpa_eq(c, t1, t2);
        RESET_ERROR_CODE();
        if (!is_fp(c, t1) || !is_fp(c, t2)) {
            SET_ERROR_CODE(Z3_INVALID_ARG, "fp sorts expected");
            RETURN_Z3(nullptr);
        }
        api::context * ctx = mk_c(c);
        expr * a = ctx->fpautil().mk_float_eq(to_expr(t1), to_expr(t2));
        ctx->save_ast_trail(a);
        RETURN_Z3(of_expr(a));
        Z3_CATCH_RETURN(nullptr);
    }

    Z3_ast Z3_API Z3_mk_fpa_is_normal(Z3_context c, Z3_ast t) {
        Z3_TRY;
        LOG_Z3_mk_fpa_is_normal(c, t);
        RESET_ERROR_CODE();
        if (!is_fp(c, t)) {
            SET_ERROR_CODE(Z3_INVALID_ARG, "fp sort expected");
            RETURN_Z3(nullptr);
        }
        api::context * ctx = mk_c(c);
        expr * a = ctx->fpautil().mk_is_normal(to_expr(t));
        ctx->save_ast_trail(a);
        RETURN_Z3(of_expr(a));
        Z3_CATCH_RETURN(nullptr);
    }

    Z3_ast Z3_API Z3_mk_fpa_is_subnormal(Z3_context c, Z3_ast t) {
        Z3_TRY;
        LOG_Z3_mk_fpa_is_subnormal(c, t);
        RESET_ERROR_CODE();
        if (!is_fp(c, t)) {
            SET_ERROR_CODE(Z3_INVALID_ARG, "fp sort expected");
            RETURN_Z3(nullptr);
        }
        api::context * ctx = mk_c(c);
        expr * a = ctx->fpautil().mk_is_subnormal(to_expr(t));
        ctx->save_ast_trail(a);
        RETURN_Z3(of_expr(a));
        Z3_CATCH_RETURN(nullptr);
    }

    Z3_ast Z3_API Z3_mk_fpa_is_zero(Z3_context c, Z3_ast t) {
        Z3_TRY;
        LOG_Z3_mk_fpa_is_zero(c, t);
        RESET_ERROR_CODE();
        if (!is_fp(c, t)) {
            SET_ERROR_CODE(Z3_INVALID_ARG, "fp sort expected");
            RETURN_Z3(nullptr);
        }
        api::context * ctx = mk_c(c);
        expr * a = ctx->fpautil().mk_is_zero(to_expr(t));
        ctx->save_ast_trail(a);
        RETURN_Z3(of_expr(a));
        Z3_CATCH_RETURN(nullptr);
    }

    Z3_ast Z3_API Z3_mk_fpa_is_infinite(Z3_context c, Z3_ast t) {
        Z3_TRY;
        LOG_Z3_mk_fpa_is_infinite(c, t);
        RESET_ERROR_CODE();
        if (!is_fp(c, t)) {
            SET_ERROR_CODE(Z3_INVALID_ARG, "fp sort expected");
            RETURN_Z3(nullptr);
        }
        api::context * ctx = mk_c(c);
        expr * a = ctx->fpautil().mk_is_inf(to_expr(t));
        ctx->save_ast_trail(a);
        RETURN_Z3(of_expr(a));
        Z3_CATCH_RETURN(nullptr);
    }

    Z3_ast Z3_API Z3_mk_fpa_is_nan(Z3_context c, Z3_ast t) {
        Z3_TRY;
        LOG_Z3_mk_fpa_is_nan(c, t);
        RESET_ERROR_CODE();
        if (!is_fp(c, t)) {
            SET_ERROR_CODE(Z3_INVALID_ARG, "fp sort expected");
            RETURN_Z3(nullptr);
        }
        api::context * ctx = mk_c(c);
        expr * a = ctx->fpautil().mk_is_nan(to_expr(t));
        ctx->save_ast_trail(a);
        RETURN_Z3(of_expr(a));
        Z3_CATCH_RETURN(nullptr);
    }

    Z3_ast Z3_API Z3_mk_fpa_is_negative(Z3_context c, Z3_ast t) {
        Z3_TRY;
        LOG_Z3_mk_fpa_is_negative(c, t);
        RESET_ERROR_CODE();
        if (!is_fp(c, t)) {
            SET_ERROR_CODE(Z3_INVALID_ARG, "fp sort expected");
            RETURN_Z3(nullptr);
        }
        api::context * ctx = mk_c(c);
        expr * a = ctx->fpautil().mk_is_negative(to_expr(t));
        ctx->save_ast_trail(a);
        RETURN_Z3(of_expr(a));
        Z3_CATCH_RETURN(nullptr);
    }

    Z3_ast Z3_API Z3_mk_fpa_is_positive(Z3_context c, Z3_ast t) {
        Z3_TRY;
        LOG_Z3_mk_fpa_is_positive(c, t);
        RESET_ERROR_CODE();
        if (!is_fp(c, t)) {
            SET_ERROR_CODE(Z3_INVALID_ARG, "fp sort expected");
            RETURN_Z3(nullptr);
        }
        api::context * ctx = mk_c(c);
        expr * a = ctx->fpautil().mk_is_positive(to_expr(t));
        ctx->save_ast_trail(a);
        RETURN_Z3(of_expr(a));
        Z3_CATCH_RETURN(nullptr);
    }


    Z3_ast Z3_API Z3_mk_fpa_to_fp_bv(Z3_context c, Z3_ast bv, Z3_sort s) {
        Z3_TRY;
        LOG_Z3_mk_fpa_to_fp_bv(c, bv, s);
        RESET_ERROR_CODE();
        if (!is_bv(c, bv) || !is_fp_sort(c, s)) {
            SET_ERROR_CODE(Z3_INVALID_ARG, "bv then fp sort expected");
            RETURN_Z3(nullptr);
        }
        api::context * ctx = mk_c(c);
        fpa_util & fu = ctx->fpautil();
        if (!ctx->bvutil().is_bv(to_expr(bv)) ||
            !fu.is_float(to_sort(s))) {
            SET_ERROR_CODE(Z3_INVALID_ARG, "bv sort the flaot sort expected");
            return nullptr;
        }
        expr * a = fu.mk_to_fp(to_sort(s), to_expr(bv));
        ctx->save_ast_trail(a);
        RETURN_Z3(of_expr(a));
        Z3_CATCH_RETURN(nullptr);
    }

    Z3_ast Z3_API Z3_mk_fpa_to_fp_float(Z3_context c, Z3_ast rm, Z3_ast t, Z3_sort s) {
        Z3_TRY;
        LOG_Z3_mk_fpa_to_fp_float(c, rm, t, s);
        RESET_ERROR_CODE();
        api::context * ctx = mk_c(c);
        fpa_util & fu = ctx->fpautil();
        if (!fu.is_rm(to_expr(rm)) ||
            !fu.is_float(to_expr(t)) ||
            !fu.is_float(to_sort(s))) {
            SET_ERROR_CODE(Z3_INVALID_ARG, "rm and float sorts expected");
            return nullptr;
        }
        expr * a = fu.mk_to_fp(to_sort(s), to_expr(rm), to_expr(t));
        ctx->save_ast_trail(a);
        RETURN_Z3(of_expr(a));
        Z3_CATCH_RETURN(nullptr);
    }

    Z3_ast Z3_API Z3_mk_fpa_to_fp_real(Z3_context c, Z3_ast rm, Z3_ast t, Z3_sort s) {
        Z3_TRY;
        LOG_Z3_mk_fpa_to_fp_real(c, rm, t, s);
        RESET_ERROR_CODE();
        api::context * ctx = mk_c(c);
        fpa_util & fu = ctx->fpautil();
        if (!fu.is_rm(to_expr(rm)) ||
            !ctx->autil().is_real(to_expr(t)) ||
            !fu.is_float(to_sort(s))) {
            SET_ERROR_CODE(Z3_INVALID_ARG, "rm and float sorts expected");
            return nullptr;
        }
        expr * a = fu.mk_to_fp(to_sort(s), to_expr(rm), to_expr(t));
        ctx->save_ast_trail(a);
        RETURN_Z3(of_expr(a));
        Z3_CATCH_RETURN(nullptr);
    }

    Z3_ast Z3_API Z3_mk_fpa_to_fp_signed(Z3_context c, Z3_ast rm, Z3_ast t, Z3_sort s) {
        Z3_TRY;
        LOG_Z3_mk_fpa_to_fp_signed(c, rm, t, s);
        RESET_ERROR_CODE();
        api::context * ctx = mk_c(c);
        fpa_util & fu = ctx->fpautil();
        if (!fu.is_rm(to_expr(rm)) ||
            !ctx->bvutil().is_bv(to_expr(t)) ||
            !fu.is_float(to_sort(s))) {
            SET_ERROR_CODE(Z3_INVALID_ARG, "rm and float sorts expected");
            return nullptr;
        }
        expr * a = fu.mk_to_fp(to_sort(s), to_expr(rm), to_expr(t));
        ctx->save_ast_trail(a);
        RETURN_Z3(of_expr(a));
        Z3_CATCH_RETURN(nullptr);
    }

    Z3_ast Z3_API Z3_mk_fpa_to_fp_unsigned(Z3_context c, Z3_ast rm, Z3_ast t, Z3_sort s) {
        Z3_TRY;
        LOG_Z3_mk_fpa_to_fp_unsigned(c, rm, t, s);
        RESET_ERROR_CODE();
        api::context * ctx = mk_c(c);
        fpa_util & fu = ctx->fpautil();
        if (!fu.is_rm(to_expr(rm)) ||
            !ctx->bvutil().is_bv(to_expr(t)) ||
            !fu.is_float(to_sort(s))) {
            SET_ERROR_CODE(Z3_INVALID_ARG, "rm and float sorts expected");
            return nullptr;
        }
        expr * a = fu.mk_to_fp_unsigned(to_sort(s), to_expr(rm), to_expr(t));
        ctx->save_ast_trail(a);
        RETURN_Z3(of_expr(a));
        Z3_CATCH_RETURN(nullptr);
    }

    Z3_ast Z3_API Z3_mk_fpa_to_ubv(Z3_context c, Z3_ast rm, Z3_ast t, unsigned sz) {
        Z3_TRY;
        LOG_Z3_mk_fpa_to_ubv(c, rm, t, sz);
        RESET_ERROR_CODE();
        if (!is_rm(c, rm) || !is_fp(c, t)) {
            SET_ERROR_CODE(Z3_INVALID_ARG, "rm and float sorts expected");
            RETURN_Z3(nullptr);
        }
        api::context * ctx = mk_c(c);
        expr * a = ctx->fpautil().mk_to_ubv(to_expr(rm), to_expr(t), sz);
        ctx->save_ast_trail(a);
        RETURN_Z3(of_expr(a));
        Z3_CATCH_RETURN(nullptr);
    }

    Z3_ast Z3_API Z3_mk_fpa_to_sbv(Z3_context c, Z3_ast rm, Z3_ast t, unsigned sz) {
        Z3_TRY;
        LOG_Z3_mk_fpa_to_sbv(c, rm, t, sz);
        RESET_ERROR_CODE();
        if (!is_rm(c, rm) || !is_fp(c, t)) {
            SET_ERROR_CODE(Z3_INVALID_ARG, "rm and float sorts expected");
            RETURN_Z3(nullptr);
        }
        api::context * ctx = mk_c(c);
        expr * a = ctx->fpautil().mk_to_sbv(to_expr(rm), to_expr(t), sz);
        ctx->save_ast_trail(a);
        RETURN_Z3(of_expr(a));
        Z3_CATCH_RETURN(nullptr);
    }

    Z3_ast Z3_API Z3_mk_fpa_to_real(Z3_context c, Z3_ast t) {
        Z3_TRY;
        LOG_Z3_mk_fpa_to_real(c, t);
        RESET_ERROR_CODE();
        if (!is_fp(c, t)) {
            SET_ERROR_CODE(Z3_INVALID_ARG, "fp sort expected");
            RETURN_Z3(nullptr);
        }
        api::context * ctx = mk_c(c);
        expr * a = ctx->fpautil().mk_to_real(to_expr(t));
        ctx->save_ast_trail(a);
        RETURN_Z3(of_expr(a));
        Z3_CATCH_RETURN(nullptr);
    }

    unsigned Z3_API Z3_fpa_get_ebits(Z3_context c, Z3_sort s) {
        Z3_TRY;
        LOG_Z3_fpa_get_ebits(c, s);
        RESET_ERROR_CODE();
        CHECK_NON_NULL(s, 0);
        CHECK_VALID_AST(s, 0);
        if (!is_fp_sort(c, s)) {
            SET_ERROR_CODE(Z3_INVALID_ARG, "fp sort expected");
            return 0;
        }
        return mk_c(c)->fpautil().get_ebits(to_sort(s));
        Z3_CATCH_RETURN(0);
    }

    unsigned Z3_API Z3_fpa_get_sbits(Z3_context c, Z3_sort s) {
        Z3_TRY;
        LOG_Z3_fpa_get_sbits(c, s);
        RESET_ERROR_CODE();
        CHECK_NON_NULL(s, 0);
        CHECK_VALID_AST(s, 0);
        if (!is_fp_sort(c, s)) {
            SET_ERROR_CODE(Z3_INVALID_ARG, "fp sort expected");
            return 0;
        }
        return mk_c(c)->fpautil().get_sbits(to_sort(s));
        Z3_CATCH_RETURN(0);
    }

    bool Z3_API Z3_fpa_get_numeral_sign(Z3_context c, Z3_ast t, int * sgn) {
        Z3_TRY;
        LOG_Z3_fpa_get_numeral_sign(c, t, sgn);
        RESET_ERROR_CODE();
        CHECK_NON_NULL(t, 0);
        CHECK_VALID_AST(t, 0);
        if (sgn == nullptr) {
            SET_ERROR_CODE(Z3_INVALID_ARG, "sign cannot be a nullpointer");
            return false;
        }
        ast_manager & m = mk_c(c)->m();
        mpf_manager & mpfm = mk_c(c)->fpautil().fm();
        family_id fid = mk_c(c)->get_fpa_fid();
        fpa_decl_plugin * plugin = (fpa_decl_plugin*)m.get_plugin(fid);
        expr * e = to_expr(t);
        if (!is_app(e) || is_app_of(e, fid, OP_FPA_NAN) || !is_fp(c, t)) {
            SET_ERROR_CODE(Z3_INVALID_ARG, "invalid expression argument, expecting a valid fp, not a NaN");
            return false;
        }
        scoped_mpf val(mpfm);
        bool r = plugin->is_numeral(to_expr(t), val);
        if (!r || mpfm.is_nan(val)) {
            SET_ERROR_CODE(Z3_INVALID_ARG, "invalid expression argument, expecting a valid fp, not a NaN");
            return false;
        }
        *sgn = mpfm.sgn(val);
        return r;
        Z3_CATCH_RETURN(0);
    }

    Z3_ast Z3_API Z3_fpa_get_numeral_sign_bv(Z3_context c, Z3_ast t) {
        Z3_TRY;
        LOG_Z3_fpa_get_numeral_sign_bv(c, t);
        RESET_ERROR_CODE();
        CHECK_NON_NULL(t, nullptr);
        CHECK_VALID_AST(t, nullptr);
        ast_manager & m = mk_c(c)->m();
        mpf_manager & mpfm = mk_c(c)->fpautil().fm();
        family_id fid = mk_c(c)->get_fpa_fid();
        fpa_decl_plugin * plugin = (fpa_decl_plugin*)m.get_plugin(fid);
        api::context * ctx = mk_c(c);
        expr * e = to_expr(t);
        if (!is_app(e) || is_app_of(e, fid, OP_FPA_NAN) || !is_fp(c, t)) {
            SET_ERROR_CODE(Z3_INVALID_ARG, "invalid expression argument, expecting a valid fp, not a NaN");
            RETURN_Z3(nullptr);
        }
        scoped_mpf val(mpfm);
        bool r = plugin->is_numeral(to_expr(t), val);
        if (!r || mpfm.is_nan(val)) {
            SET_ERROR_CODE(Z3_INVALID_ARG, "invalid expression argument, expecting a valid fp, not a NaN");
            return nullptr;
        }
        app * a;
        if (mpfm.is_pos(val))
            a = ctx->bvutil().mk_numeral(0, 1);
        else
            a = ctx->bvutil().mk_numeral(1, 1);
        mk_c(c)->save_ast_trail(a);
        RETURN_Z3(of_expr(a));
        Z3_CATCH_RETURN(nullptr);
    }

    Z3_ast Z3_API Z3_fpa_get_numeral_significand_bv(Z3_context c, Z3_ast t) {
        Z3_TRY;
        LOG_Z3_fpa_get_numeral_significand_bv(c, t);
        RESET_ERROR_CODE();
        CHECK_NON_NULL(t, nullptr);
        CHECK_VALID_AST(t, nullptr);
        ast_manager & m = mk_c(c)->m();
        mpf_manager & mpfm = mk_c(c)->fpautil().fm();
        unsynch_mpq_manager & mpqm = mpfm.mpq_manager();
        family_id fid = mk_c(c)->get_fpa_fid();
        fpa_decl_plugin * plugin = (fpa_decl_plugin*)m.get_plugin(fid);
        SASSERT(plugin != 0);
        expr * e = to_expr(t);
        if (!is_app(e) || is_app_of(e, fid, OP_FPA_NAN) || !is_fp(c, t)) {
            SET_ERROR_CODE(Z3_INVALID_ARG, "invalid expression argument, expecting a valid fp, not a NaN");
            RETURN_Z3(nullptr);
        }
        scoped_mpf val(mpfm);
        bool r = plugin->is_numeral(e, val);
        if (!r || !(mpfm.is_normal(val) || mpfm.is_denormal(val) || mpfm.is_zero(val) || mpfm.is_inf(val))) {
            SET_ERROR_CODE(Z3_INVALID_ARG, "invalid expression argument, expecting a valid fp, not a NaN");
            RETURN_Z3(nullptr);
        }
        unsigned sbits = val.get().get_sbits();
        scoped_mpq q(mpqm);
        mpqm.set(q, mpfm.sig(val));
        if (mpfm.is_inf(val)) mpqm.set(q, 0);
        app * a = mk_c(c)->bvutil().mk_numeral(q.get(), sbits-1);
        mk_c(c)->save_ast_trail(a);
        RETURN_Z3(of_expr(a));
        Z3_CATCH_RETURN(nullptr);
    }

    Z3_string Z3_API Z3_fpa_get_numeral_significand_string(Z3_context c, Z3_ast t) {
        Z3_TRY;
        LOG_Z3_fpa_get_numeral_significand_string(c, t);
        RESET_ERROR_CODE();
        CHECK_NON_NULL(t, nullptr);
        CHECK_VALID_AST(t, nullptr);
        ast_manager & m = mk_c(c)->m();
        mpf_manager & mpfm = mk_c(c)->fpautil().fm();
        unsynch_mpq_manager & mpqm = mpfm.mpq_manager();
        family_id fid = mk_c(c)->get_fpa_fid();
        fpa_decl_plugin * plugin = (fpa_decl_plugin*)m.get_plugin(fid);
        SASSERT(plugin != 0);
        expr * e = to_expr(t);
        if (!is_app(e) || is_app_of(e, fid, OP_FPA_NAN) || !is_fp(c, t)) {
            SET_ERROR_CODE(Z3_INVALID_ARG, "invalid expression argument, expecting a valid fp, not a NaN");
            return "";
        }
        scoped_mpf val(mpfm);
        bool r = plugin->is_numeral(e, val);
        if (!r || !(mpfm.is_normal(val) || mpfm.is_denormal(val) || mpfm.is_zero(val) || mpfm.is_inf(val))) {
            SET_ERROR_CODE(Z3_INVALID_ARG, "invalid expression argument, expecting a valid fp, not a NaN");
            return "";
        }
        unsigned sbits = val.get().get_sbits();
        scoped_mpq q(mpqm);
        mpqm.set(q, mpfm.sig(val));
        if (!mpfm.is_denormal(val)) mpqm.add(q, mpfm.m_powers2(sbits - 1), q);
        mpqm.div(q, mpfm.m_powers2(sbits - 1), q);
        if (mpfm.is_inf(val)) mpqm.set(q, 0);
        std::stringstream ss;
        mpqm.display_decimal(ss, q, sbits);
        return mk_c(c)->mk_external_string(ss.str());
        Z3_CATCH_RETURN("");
    }

    bool Z3_API Z3_fpa_get_numeral_significand_uint64(Z3_context c, Z3_ast t, uint64_t * n) {
        Z3_TRY;
        LOG_Z3_fpa_get_numeral_significand_uint64(c, t, n);
        RESET_ERROR_CODE();
        CHECK_NON_NULL(t, 0);
        CHECK_VALID_AST(t, 0);
        if (n == nullptr) {
            SET_ERROR_CODE(Z3_INVALID_ARG, "invalid nullptr argument");
            return false;
        }
        ast_manager & m = mk_c(c)->m();
        mpf_manager & mpfm = mk_c(c)->fpautil().fm();
        unsynch_mpz_manager & mpzm = mpfm.mpz_manager();
        family_id fid = mk_c(c)->get_fpa_fid();
        fpa_decl_plugin * plugin = (fpa_decl_plugin*)m.get_plugin(fid);
        SASSERT(plugin != 0);
        expr * e = to_expr(t);
        if (!is_app(e) || is_app_of(e, fid, OP_FPA_NAN) || !is_fp(c, t)) {
            SET_ERROR_CODE(Z3_INVALID_ARG, "invalid expression argument, expecting a valid fp, not a NaN");
            *n = 0;
            return false;
        }
        scoped_mpf val(mpfm);
        bool r = plugin->is_numeral(e, val);
        const mpz & z = mpfm.sig(val);
        if (!r ||
            !(mpfm.is_normal(val) || mpfm.is_denormal(val) || mpfm.is_zero(val) || mpfm.is_inf(val)) ||
            !mpzm.is_uint64(z)) {
            SET_ERROR_CODE(Z3_INVALID_ARG, "invalid expression argument, expecting a valid fp, not a NaN");
            *n = 0;
            return false;
        }
        *n = mpzm.get_uint64(z);
        return true;
        Z3_CATCH_RETURN(0);
    }

    Z3_string Z3_API Z3_fpa_get_numeral_exponent_string(Z3_context c, Z3_ast t, bool biased) {
        Z3_TRY;
        LOG_Z3_fpa_get_numeral_exponent_string(c, t, biased);
        RESET_ERROR_CODE();
        CHECK_NON_NULL(t, nullptr);
        CHECK_VALID_AST(t, nullptr);
        ast_manager & m = mk_c(c)->m();
        mpf_manager & mpfm = mk_c(c)->fpautil().fm();
        family_id fid = mk_c(c)->get_fpa_fid();
        fpa_decl_plugin * plugin = (fpa_decl_plugin*)m.get_plugin(mk_c(c)->get_fpa_fid());
        SASSERT(plugin != 0);
        expr * e = to_expr(t);
        if (!is_app(e) || is_app_of(e, fid, OP_FPA_NAN) || !is_fp(c, t)) {
            SET_ERROR_CODE(Z3_INVALID_ARG, "invalid expression argument, expecting a valid fp, not a NaN");
            return "";
        }
        scoped_mpf val(mpfm);
        bool r = plugin->is_numeral(e, val);
        if (!r || !(mpfm.is_normal(val) || mpfm.is_denormal(val) || mpfm.is_zero(val) || mpfm.is_inf(val))) {
            SET_ERROR_CODE(Z3_INVALID_ARG, "invalid expression argument, expecting a valid fp, not a NaN");
            return "";
        }
        unsigned ebits = val.get().get_ebits();
        mpf_exp_t exp;
        if (biased) {
            exp = mpfm.is_zero(val) ? 0 :
                  mpfm.is_inf(val) ? mpfm.mk_top_exp(ebits) :
                  mpfm.bias_exp(ebits, mpfm.exp(val));
        }
        else {
            exp = mpfm.is_zero(val) ? 0 :
                  mpfm.is_inf(val) ? mpfm.mk_top_exp(ebits) :
                  mpfm.is_denormal(val) ? mpfm.mk_min_exp(ebits) :
                  mpfm.exp(val);
        }
        std::stringstream ss;
        ss << exp;
        return mk_c(c)->mk_external_string(ss.str());
        Z3_CATCH_RETURN("");
    }

    bool Z3_API Z3_fpa_get_numeral_exponent_int64(Z3_context c, Z3_ast t, int64_t * n, bool biased) {
        Z3_TRY;
        LOG_Z3_fpa_get_numeral_exponent_int64(c, t, n, biased);
        RESET_ERROR_CODE();
        CHECK_NON_NULL(t, 0);
        CHECK_VALID_AST(t, 0);
        if (n == nullptr) {
            SET_ERROR_CODE(Z3_INVALID_ARG, "invalid null argument");
            return false;
        }
        ast_manager & m = mk_c(c)->m();
        mpf_manager & mpfm = mk_c(c)->fpautil().fm();
        family_id fid = mk_c(c)->get_fpa_fid();
        fpa_decl_plugin * plugin = (fpa_decl_plugin*)m.get_plugin(mk_c(c)->get_fpa_fid());
        SASSERT(plugin != 0);
        expr * e = to_expr(t);
        if (!is_app(e) || is_app_of(e, fid, OP_FPA_NAN) || !is_fp(c, t)) {
            SET_ERROR_CODE(Z3_INVALID_ARG, "invalid expression argument, expecting a valid fp, not a NaN");
            *n = 0;
            return false;
        }
        scoped_mpf val(mpfm);
        bool r = plugin->is_numeral(e, val);
        if (!r || !(mpfm.is_normal(val) || mpfm.is_denormal(val) || mpfm.is_zero(val) || mpfm.is_inf(val))) {
            SET_ERROR_CODE(Z3_INVALID_ARG, "invalid expression argument, expecting a valid fp, not a NaN");
            *n = 0;
            return false;
        }
        unsigned ebits = val.get().get_ebits();
        if (biased) {
            *n = mpfm.is_zero(val) ? 0 :
                 mpfm.is_inf(val) ? mpfm.mk_top_exp(ebits) :
                 mpfm.bias_exp(ebits, mpfm.exp(val));
        }
        else {
            *n = mpfm.is_zero(val) ? 0 :
                 mpfm.is_inf(val) ? mpfm.mk_top_exp(ebits) :
                  mpfm.is_denormal(val) ? mpfm.mk_min_exp(ebits) :
                 mpfm.exp(val);
        }
        return true;
        Z3_CATCH_RETURN(0);
    }

    Z3_ast Z3_API Z3_fpa_get_numeral_exponent_bv(Z3_context c, Z3_ast t, bool biased) {
        Z3_TRY;
        LOG_Z3_fpa_get_numeral_exponent_bv(c, t, biased);
        RESET_ERROR_CODE();
        CHECK_NON_NULL(t, nullptr);
        CHECK_VALID_AST(t, nullptr);
        ast_manager & m = mk_c(c)->m();
        mpf_manager & mpfm = mk_c(c)->fpautil().fm();
        family_id fid = mk_c(c)->get_fpa_fid();
        fpa_decl_plugin * plugin = (fpa_decl_plugin*)m.get_plugin(fid);
        expr * e = to_expr(t);
        if (!is_app(e) || is_app_of(e, fid, OP_FPA_NAN) || !is_fp(c, t)) {
            SET_ERROR_CODE(Z3_INVALID_ARG, "invalid expression argument, expecting a valid fp, not a NaN");
            RETURN_Z3(nullptr);
        }
        scoped_mpf val(mpfm);
        bool r = plugin->is_numeral(e, val);
        if (!r || !(mpfm.is_normal(val) || mpfm.is_denormal(val) || mpfm.is_zero(val) || mpfm.is_inf(val))) {
            SET_ERROR_CODE(Z3_INVALID_ARG, "invalid expression argument, expecting a valid fp, not a NaN");
            RETURN_Z3(nullptr);
        }
        unsigned ebits = val.get().get_ebits();
        mpf_exp_t exp;
        if (biased) {
            exp = mpfm.is_zero(val) ? 0 :
                  mpfm.is_inf(val) ? mpfm.mk_top_exp(ebits) :
                  mpfm.bias_exp(ebits, mpfm.exp(val));
        }
        else {
            exp = mpfm.is_zero(val) ? 0 :
                  mpfm.is_inf(val) ? mpfm.mk_top_exp(ebits) :
                  mpfm.is_denormal(val) ? mpfm.mk_min_exp(ebits) :
                  mpfm.exp(val);
        }
        app * a = mk_c(c)->bvutil().mk_numeral(exp, ebits);
        mk_c(c)->save_ast_trail(a);
        RETURN_Z3(of_expr(a));
        Z3_CATCH_RETURN(nullptr);
    }

    Z3_ast Z3_API Z3_mk_fpa_to_ieee_bv(Z3_context c, Z3_ast t) {
        Z3_TRY;
        LOG_Z3_mk_fpa_to_ieee_bv(c, t);
        RESET_ERROR_CODE();
        CHECK_NON_NULL(t, nullptr);
        CHECK_VALID_AST(t, nullptr);
        if (!is_fp(c, t)) {
            SET_ERROR_CODE(Z3_INVALID_ARG, "fp sort expected");
            RETURN_Z3(nullptr);
        }
        api::context * ctx = mk_c(c);
        expr * r = ctx->fpautil().mk_to_ieee_bv(to_expr(t));
        ctx->save_ast_trail(r);
        RETURN_Z3(of_expr(r));
        Z3_CATCH_RETURN(nullptr);
    }

    Z3_ast Z3_API Z3_mk_fpa_to_fp_int_real(Z3_context c, Z3_ast rm, Z3_ast exp, Z3_ast sig, Z3_sort s) {
        Z3_TRY;
        LOG_Z3_mk_fpa_to_fp_int_real(c, rm, exp, sig, s);
        RESET_ERROR_CODE();
        api::context * ctx = mk_c(c);
        fpa_util & fu = ctx->fpautil();
        if (!fu.is_rm(to_expr(rm)) ||
            !ctx->autil().is_int(to_expr(exp)) ||
            !ctx->autil().is_real(to_expr(sig)) ||
            !fu.is_float(to_sort(s))) {
            SET_ERROR_CODE(Z3_INVALID_ARG, nullptr);
            return nullptr;
        }
        expr * a = fu.mk_to_fp(to_sort(s), to_expr(rm), to_expr(exp), to_expr(sig));
        ctx->save_ast_trail(a);
        RETURN_Z3(of_expr(a));
        Z3_CATCH_RETURN(nullptr);
    }

    bool Z3_API Z3_fpa_is_numeral_nan(Z3_context c, Z3_ast t) {
        Z3_TRY;
        LOG_Z3_fpa_is_numeral_nan(c, t);
        RESET_ERROR_CODE();
        api::context * ctx = mk_c(c);
        fpa_util & fu = ctx->fpautil();
        if (!is_expr(t) || !fu.is_numeral(to_expr(t))) {
            SET_ERROR_CODE(Z3_INVALID_ARG, nullptr);
            return false;
        }
        return fu.is_nan(to_expr(t));
        Z3_CATCH_RETURN(false);
    }

    bool Z3_API Z3_fpa_is_numeral_inf(Z3_context c, Z3_ast t) {
        Z3_TRY;
        LOG_Z3_fpa_is_numeral_inf(c, t);
        RESET_ERROR_CODE();
        api::context * ctx = mk_c(c);
        fpa_util & fu = ctx->fpautil();
        if (!is_expr(t) || !fu.is_numeral(to_expr(t))) {
            SET_ERROR_CODE(Z3_INVALID_ARG, nullptr);
            return false;
        }
        return fu.is_inf(to_expr(t));
        Z3_CATCH_RETURN(false);
    }

    bool Z3_API Z3_fpa_is_numeral_zero(Z3_context c, Z3_ast t) {
        Z3_TRY;
        LOG_Z3_fpa_is_numeral_zero(c, t);
        RESET_ERROR_CODE();
        api::context * ctx = mk_c(c);
        fpa_util & fu = ctx->fpautil();
        if (!is_expr(t) || !fu.is_numeral(to_expr(t))) {
            SET_ERROR_CODE(Z3_INVALID_ARG, nullptr);
            return false;
        }
        return fu.is_zero(to_expr(t));
        Z3_CATCH_RETURN(false);
    }

    bool Z3_API Z3_fpa_is_numeral_normal(Z3_context c, Z3_ast t) {
        Z3_TRY;
        LOG_Z3_fpa_is_numeral_normal(c, t);
        RESET_ERROR_CODE();
        api::context * ctx = mk_c(c);
        fpa_util & fu = ctx->fpautil();
        if (!is_expr(t) || !fu.is_numeral(to_expr(t))) {
            SET_ERROR_CODE(Z3_INVALID_ARG, nullptr);
            return false;
        }
        return fu.is_normal(to_expr(t));
        Z3_CATCH_RETURN(false);
    }

    bool Z3_API Z3_fpa_is_numeral_subnormal(Z3_context c, Z3_ast t) {
        Z3_TRY;
        LOG_Z3_fpa_is_numeral_subnormal(c, t);
        RESET_ERROR_CODE();
        api::context * ctx = mk_c(c);
        fpa_util & fu = ctx->fpautil();
        if (!is_expr(t) || !fu.is_numeral(to_expr(t))) {
            SET_ERROR_CODE(Z3_INVALID_ARG, nullptr);
            return false;
        }
        return fu.is_subnormal(to_expr(t));
        Z3_CATCH_RETURN(false);
    }

    bool Z3_API Z3_fpa_is_numeral_positive(Z3_context c, Z3_ast t) {
        Z3_TRY;
        LOG_Z3_fpa_is_numeral_positive(c, t);
        RESET_ERROR_CODE();
        api::context * ctx = mk_c(c);
        fpa_util & fu = ctx->fpautil();
        if (!is_expr(t) || !fu.is_numeral(to_expr(t))) {
            SET_ERROR_CODE(Z3_INVALID_ARG, nullptr);
            return false;
        }
        return fu.is_positive(to_expr(t));
        Z3_CATCH_RETURN(false);
    }

    bool Z3_API Z3_fpa_is_numeral_negative(Z3_context c, Z3_ast t) {
        Z3_TRY;
        LOG_Z3_fpa_is_numeral_negative(c, t);
        RESET_ERROR_CODE();
        api::context * ctx = mk_c(c);
        fpa_util & fu = ctx->fpautil();
        if (!is_expr(t) || !fu.is_numeral(to_expr(t))) {
            SET_ERROR_CODE(Z3_INVALID_ARG, nullptr);
            return false;
        }
        return fu.is_negative(to_expr(t));
        Z3_CATCH_RETURN(false);
    }

};
