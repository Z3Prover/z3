/*++
Copyright (c) 2013 Microsoft Corporation

Module Name:

    api_fpa.cpp

Abstract:


Author:

    Christoph M. Wintersteiger (cwinter) 2013-06-05

Notes:
    
--*/
#include<iostream>
#include"z3.h"
#include"api_log_macros.h"
#include"api_context.h"
#include"float_decl_plugin.h"

extern "C" {

    Z3_sort Z3_API Z3_mk_fpa_rounding_mode_sort(Z3_context c) {
        Z3_TRY;
        LOG_Z3_mk_fpa_rounding_mode_sort(c);
        RESET_ERROR_CODE(); 
        api::context * ctx = mk_c(c);        
        Z3_sort r = of_sort(float_util(ctx->m()).mk_rm_sort());
        RETURN_Z3(r);
        Z3_CATCH_RETURN(0);
    }   

    Z3_ast Z3_API Z3_mk_fpa_round_nearest_ties_to_even(Z3_context c)
    {
        Z3_TRY;
        LOG_Z3_mk_fpa_round_nearest_ties_to_even(c);
        RESET_ERROR_CODE(); 
        api::context * ctx = mk_c(c);
        Z3_ast r = of_ast(float_util(ctx->m()).mk_round_nearest_ties_to_even());
        RETURN_Z3(r);
        Z3_CATCH_RETURN(0);
    }

    Z3_ast Z3_API Z3_mk_fpa_round_nearest_ties_to_away(Z3_context c)
    {
        Z3_TRY;
        LOG_Z3_mk_fpa_round_nearest_ties_to_even(c);
        RESET_ERROR_CODE(); 
        api::context * ctx = mk_c(c);
        Z3_ast r = of_ast(float_util(ctx->m()).mk_round_nearest_ties_to_away());
        RETURN_Z3(r);
        Z3_CATCH_RETURN(0);
    }

    Z3_ast Z3_API Z3_mk_fpa_round_toward_positive(Z3_context c)
    {
        Z3_TRY;
        LOG_Z3_mk_fpa_round_nearest_ties_to_even(c);
        RESET_ERROR_CODE(); 
        api::context * ctx = mk_c(c);
        Z3_ast r = of_ast(float_util(ctx->m()).mk_round_toward_positive());
        RETURN_Z3(r);
        Z3_CATCH_RETURN(0);
    }

    Z3_ast Z3_API Z3_mk_fpa_round_toward_negative(Z3_context c)
    {
        Z3_TRY;
        LOG_Z3_mk_fpa_round_nearest_ties_to_even(c);
        RESET_ERROR_CODE(); 
        api::context * ctx = mk_c(c);
        Z3_ast r = of_ast(float_util(ctx->m()).mk_round_toward_negative());
        RETURN_Z3(r);
        Z3_CATCH_RETURN(0);
    }

    Z3_ast Z3_API Z3_mk_fpa_round_toward_zero(Z3_context c)
    {
        Z3_TRY;
        LOG_Z3_mk_fpa_round_nearest_ties_to_even(c);
        RESET_ERROR_CODE(); 
        api::context * ctx = mk_c(c);
        Z3_ast r = of_ast(float_util(ctx->m()).mk_round_toward_zero());
        RETURN_Z3(r);
        Z3_CATCH_RETURN(0);
    }

    Z3_sort Z3_API Z3_mk_fpa_sort(Z3_context c, unsigned ebits, unsigned sbits) {
        Z3_TRY;
        LOG_Z3_mk_fpa_sort(c, ebits, sbits);
        RESET_ERROR_CODE(); 
        if (ebits < 2 || sbits < 3) {
            SET_ERROR_CODE(Z3_INVALID_ARG);
        }        
        api::context * ctx = mk_c(c);
        float_util fu(ctx->m());
        Z3_sort r = of_sort(fu.mk_float_sort(ebits, sbits));
        RETURN_Z3(r);
        Z3_CATCH_RETURN(0);
    }   

    Z3_ast Z3_API Z3_mk_fpa_nan(Z3_context c, Z3_sort s) {
        Z3_TRY;
        LOG_Z3_mk_fpa_nan(c, s);
        RESET_ERROR_CODE();         
        api::context * ctx = mk_c(c);
        Z3_ast r = of_ast(float_util(ctx->m()).mk_nan(to_sort(s)));
        RETURN_Z3(r);
        Z3_CATCH_RETURN(0);
    }
    
    Z3_ast Z3_API Z3_mk_fpa_inf(Z3_context c, Z3_sort s, Z3_bool negative) {
        Z3_TRY;
        LOG_Z3_mk_fpa_inf(c, s, negative);
        RESET_ERROR_CODE();
        api::context * ctx = mk_c(c);
        float_util fu(ctx->m());
        Z3_ast r = of_ast(negative != 0 ? fu.mk_minus_inf(to_sort(s)) : fu.mk_plus_inf(to_sort(s)));
        RETURN_Z3(r);
        Z3_CATCH_RETURN(0);
    }
    
    Z3_ast Z3_API Z3_mk_fpa_abs(Z3_context c, Z3_ast t) {
        Z3_TRY;
        LOG_Z3_mk_fpa_abs(c, t);
        RESET_ERROR_CODE();
        api::context * ctx = mk_c(c);
        Z3_ast r = of_ast(float_util(ctx->m()).mk_abs(to_expr(t)));
        RETURN_Z3(r);
        Z3_CATCH_RETURN(0);
    }
   
    Z3_ast Z3_API Z3_mk_fpa_neg(Z3_context c, Z3_ast t) {
        Z3_TRY;
        LOG_Z3_mk_fpa_neg(c, t);
        RESET_ERROR_CODE();
        api::context * ctx = mk_c(c);
        Z3_ast r = of_ast(float_util(ctx->m()).mk_uminus(to_expr(t)));
        RETURN_Z3(r);
        Z3_CATCH_RETURN(0);
    }
   
    Z3_ast Z3_API Z3_mk_fpa_add(Z3_context c, Z3_ast rm, Z3_ast t1, Z3_ast t2) {
        Z3_TRY;
        LOG_Z3_mk_fpa_add(c, rm, t1, t2);
        RESET_ERROR_CODE();
        api::context * ctx = mk_c(c);
        Z3_ast r = of_ast(float_util(ctx->m()).mk_add(to_expr(rm), to_expr(t1), to_expr(t2)));
        RETURN_Z3(r);
        Z3_CATCH_RETURN(0);
    }
   
    Z3_ast Z3_API Z3_mk_fpa_sub(Z3_context c, Z3_ast rm, Z3_ast t1, Z3_ast t2) {
        Z3_TRY;
        LOG_Z3_mk_fpa_add(c, rm, t1, t2);
        RESET_ERROR_CODE();
        api::context * ctx = mk_c(c);
        Z3_ast r = of_ast(float_util(ctx->m()).mk_sub(to_expr(rm), to_expr(t1), to_expr(t2)));
        RETURN_Z3(r);
        Z3_CATCH_RETURN(0);
    }
   
    Z3_ast Z3_API Z3_mk_fpa_mul(Z3_context c, Z3_ast rm, Z3_ast t1, Z3_ast t2) {
        Z3_TRY;
        LOG_Z3_mk_fpa_add(c, rm, t1, t2);
        RESET_ERROR_CODE();
        api::context * ctx = mk_c(c);
        Z3_ast r = of_ast(float_util(ctx->m()).mk_mul(to_expr(rm), to_expr(t1), to_expr(t2)));
        RETURN_Z3(r);
        Z3_CATCH_RETURN(0);
    }
   
    Z3_ast Z3_API Z3_mk_fpa_div(Z3_context c, Z3_ast rm, Z3_ast t1, Z3_ast t2) {
        Z3_TRY;
        LOG_Z3_mk_fpa_add(c, rm, t1, t2);
        RESET_ERROR_CODE();
        api::context * ctx = mk_c(c);
        Z3_ast r = of_ast(float_util(ctx->m()).mk_div(to_expr(rm), to_expr(t1), to_expr(t2)));
        RETURN_Z3(r);
        Z3_CATCH_RETURN(0);
    }
   
    Z3_ast Z3_API Z3_mk_fpa_fma(Z3_context c, Z3_ast rm, Z3_ast t1, Z3_ast t2, Z3_ast t3) {
        Z3_TRY;
        LOG_Z3_mk_fpa_fma(c, rm, t1, t2, t3);
        RESET_ERROR_CODE();
        api::context * ctx = mk_c(c);
        Z3_ast r = of_ast(float_util(ctx->m()).mk_fused_ma(to_expr(rm), to_expr(t1), to_expr(t2), to_expr(t3)));
        RETURN_Z3(r);
        Z3_CATCH_RETURN(0);
    }
   
    Z3_ast Z3_API Z3_mk_fpa_sqrt(Z3_context c, Z3_ast rm, Z3_ast t) {
        Z3_TRY;
        LOG_Z3_mk_fpa_sqrt(c, rm, t);
        RESET_ERROR_CODE();
        api::context * ctx = mk_c(c);
        Z3_ast r = of_ast(float_util(ctx->m()).mk_sqrt(to_expr(rm), to_expr(t)));
        RETURN_Z3(r);
        Z3_CATCH_RETURN(0);
    }
   
    Z3_ast Z3_API Z3_mk_fpa_rem(Z3_context c, Z3_ast t1, Z3_ast t2) {
        Z3_TRY;
        LOG_Z3_mk_fpa_rem(c, t1, t2);
        RESET_ERROR_CODE();
        api::context * ctx = mk_c(c);
        Z3_ast r = of_ast(float_util(ctx->m()).mk_rem(to_expr(t1), to_expr(t2)));
        RETURN_Z3(r);
        Z3_CATCH_RETURN(0);
    }
   
    Z3_ast Z3_API Z3_mk_fpa_eq(Z3_context c, Z3_ast t1, Z3_ast t2) {
        Z3_TRY;
        LOG_Z3_mk_fpa_eq(c, t1, t2);
        RESET_ERROR_CODE();
        api::context * ctx = mk_c(c);
        Z3_ast r = of_ast(float_util(ctx->m()).mk_float_eq(to_expr(t1), to_expr(t2)));
        RETURN_Z3(r);
        Z3_CATCH_RETURN(0);
    }
   
    Z3_ast Z3_API Z3_mk_fpa_leq(Z3_context c, Z3_ast t1, Z3_ast t2) {
        Z3_TRY;
        LOG_Z3_mk_fpa_leq(c, t1, t2);
        RESET_ERROR_CODE();
        api::context * ctx = mk_c(c);
        Z3_ast r = of_ast(float_util(ctx->m()).mk_le(to_expr(t1), to_expr(t2)));
        RETURN_Z3(r);
        Z3_CATCH_RETURN(0);
    }

    Z3_ast Z3_API Z3_mk_fpa_lt(Z3_context c, Z3_ast t1, Z3_ast t2) {
        Z3_TRY;
        LOG_Z3_mk_fpa_lt(c, t1, t2);
        RESET_ERROR_CODE();
        api::context * ctx = mk_c(c);
        Z3_ast r = of_ast(float_util(ctx->m()).mk_lt(to_expr(t1), to_expr(t2)));
        RETURN_Z3(r);
        Z3_CATCH_RETURN(0);
    }
    
    Z3_ast Z3_API Z3_mk_fpa_geq(Z3_context c, Z3_ast t1, Z3_ast t2) {
        Z3_TRY;
        LOG_Z3_mk_fpa_geq(c, t1, t2);
        RESET_ERROR_CODE();
        api::context * ctx = mk_c(c);
        Z3_ast r = of_ast(float_util(ctx->m()).mk_ge(to_expr(t1), to_expr(t2)));
        RETURN_Z3(r);
        Z3_CATCH_RETURN(0);
    }

    Z3_ast Z3_API Z3_mk_fpa_gt(Z3_context c, Z3_ast t1, Z3_ast t2) {
        Z3_TRY;
        LOG_Z3_mk_fpa_gt(c, t1, t2);
        RESET_ERROR_CODE();
        api::context * ctx = mk_c(c);
        Z3_ast r = of_ast(float_util(ctx->m()).mk_gt(to_expr(t1), to_expr(t2)));
        RETURN_Z3(r);
        Z3_CATCH_RETURN(0);
    }
   
    Z3_ast Z3_API Z3_mk_fpa_is_normal(Z3_context c, Z3_ast t) {
        Z3_TRY;
        LOG_Z3_mk_fpa_is_normal(c, t);
        RESET_ERROR_CODE();
        api::context * ctx = mk_c(c);
        Z3_ast r = of_ast(float_util(ctx->m()).mk_is_normal(to_expr(t)));
        RETURN_Z3(r);
        Z3_CATCH_RETURN(0);
    }

    Z3_ast Z3_API Z3_mk_fpa_is_subnormal(Z3_context c, Z3_ast t) {
        Z3_TRY;
        LOG_Z3_mk_fpa_is_subnormal(c, t);
        RESET_ERROR_CODE();
        api::context * ctx = mk_c(c);
        Z3_ast r = of_ast(float_util(ctx->m()).mk_is_subnormal(to_expr(t)));
        RETURN_Z3(r);
        Z3_CATCH_RETURN(0);
    }

    Z3_ast Z3_API Z3_mk_fpa_is_zero(Z3_context c, Z3_ast t) {
        Z3_TRY;
        LOG_Z3_mk_fpa_is_zero(c, t);
        RESET_ERROR_CODE();
        api::context * ctx = mk_c(c);
        Z3_ast r = of_ast(float_util(ctx->m()).mk_is_zero(to_expr(t)));
        RETURN_Z3(r);
        Z3_CATCH_RETURN(0);
    }

    Z3_ast Z3_API Z3_mk_fpa_is_inf(Z3_context c, Z3_ast t) {
        Z3_TRY;
        LOG_Z3_mk_fpa_is_inf(c, t);
        RESET_ERROR_CODE();
        api::context * ctx = mk_c(c);
        Z3_ast r = of_ast(float_util(ctx->m()).mk_is_inf(to_expr(t)));
        RETURN_Z3(r);
        Z3_CATCH_RETURN(0);
    }

    Z3_ast Z3_API Z3_mk_fpa_is_nan(Z3_context c, Z3_ast t) {
        Z3_TRY;
        LOG_Z3_mk_fpa_is_nan(c, t);
        RESET_ERROR_CODE();
        api::context * ctx = mk_c(c);
        Z3_ast r = of_ast(float_util(ctx->m()).mk_is_nan(to_expr(t)));
        RETURN_Z3(r);
        Z3_CATCH_RETURN(0);
    }

    Z3_ast Z3_API Z3_mk_fpa_min(Z3_context c, Z3_ast t1, Z3_ast t2) {
        Z3_TRY;
        LOG_Z3_mk_fpa_min(c, t1, t2);
        RESET_ERROR_CODE();
        api::context * ctx = mk_c(c);
        Z3_ast r = of_ast(float_util(ctx->m()).mk_min(to_expr(t1), to_expr(t2)));
        RETURN_Z3(r);
        Z3_CATCH_RETURN(0);
    }
   
    Z3_ast Z3_API Z3_mk_fpa_max(Z3_context c, Z3_ast t1, Z3_ast t2) {
        Z3_TRY;
        LOG_Z3_mk_fpa_max(c, t1, t2);
        RESET_ERROR_CODE();
        api::context * ctx = mk_c(c);
        Z3_ast r = of_ast(float_util(ctx->m()).mk_max(to_expr(t1), to_expr(t2)));
        RETURN_Z3(r);
        Z3_CATCH_RETURN(0);
    }

    Z3_ast Z3_API Z3_mk_fpa_convert(Z3_context c, Z3_sort s, Z3_ast rm, Z3_ast t) {
        Z3_TRY;
        LOG_Z3_mk_fpa_convert(c, s, rm, t);
        RESET_ERROR_CODE();
        api::context * ctx = mk_c(c);
        float_util fu(ctx->m());
        expr * args [2] = { to_expr(rm), to_expr(t) };
        Z3_ast r = of_ast(ctx->m().mk_app(fu.get_family_id(), OP_TO_FLOAT, 
                                          to_sort(s)->get_num_parameters(), to_sort(s)->get_parameters(),
                                          2, args));
        RETURN_Z3(r);
        Z3_CATCH_RETURN(0);
    }

};
