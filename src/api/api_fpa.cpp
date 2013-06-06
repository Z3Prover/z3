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

    Z3_ast Z3_API Z3_mk_fpa_round_nearest_ties_to_even(__in Z3_context c)
    {
        Z3_TRY;
        LOG_Z3_mk_fpa_round_nearest_ties_to_even(c);
        RESET_ERROR_CODE(); 
        api::context * ctx = mk_c(c);
        Z3_ast r = of_ast(float_util(ctx->m()).mk_round_nearest_ties_to_even());
        RETURN_Z3(r);
        Z3_CATCH_RETURN(0);
    }

    Z3_ast Z3_API Z3_mk_fpa_round_nearest_ties_to_away(__in Z3_context c)
    {
        Z3_TRY;
        LOG_Z3_mk_fpa_round_nearest_ties_to_even(c);
        RESET_ERROR_CODE(); 
        api::context * ctx = mk_c(c);
        Z3_ast r = of_ast(float_util(ctx->m()).mk_round_nearest_ties_to_away());
        RETURN_Z3(r);
        Z3_CATCH_RETURN(0);
    }

    Z3_ast Z3_API Z3_mk_fpa_round_toward_positive(__in Z3_context c)
    {
        Z3_TRY;
        LOG_Z3_mk_fpa_round_nearest_ties_to_even(c);
        RESET_ERROR_CODE(); 
        api::context * ctx = mk_c(c);
        Z3_ast r = of_ast(float_util(ctx->m()).mk_round_toward_positive());
        RETURN_Z3(r);
        Z3_CATCH_RETURN(0);
    }

    Z3_ast Z3_API Z3_mk_fpa_round_toward_negative(__in Z3_context c)
    {
        Z3_TRY;
        LOG_Z3_mk_fpa_round_nearest_ties_to_even(c);
        RESET_ERROR_CODE(); 
        api::context * ctx = mk_c(c);
        Z3_ast r = of_ast(float_util(ctx->m()).mk_round_toward_negative());
        RETURN_Z3(r);
        Z3_CATCH_RETURN(0);
    }

    Z3_ast Z3_API Z3_mk_fpa_round_toward_zero(__in Z3_context c)
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



};
