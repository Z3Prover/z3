/*++
Copyright (c) 2013 Microsoft Corporation

Module Name:

    api_pb.cpp

Abstract:
    API for pb theory

Author:

    Nikolaj Bjorner (nbjorner) 2013-11-13.

Revision History:

--*/
#include<iostream>
#include"z3.h"
#include"api_log_macros.h"
#include"api_context.h"
#include"api_util.h"
#include"card_decl_plugin.h"

extern "C" {
    
    Z3_ast Z3_API Z3_mk_atmost(Z3_context c, unsigned num_args, 
                               Z3_ast const args[], unsigned k) {
        Z3_TRY;
        LOG_Z3_mk_atmost(c, num_args, args, k);
        RESET_ERROR_CODE();
        parameter param(k);
        card_util util(mk_c(c)->m());
        ast* a = util.mk_at_most_k(num_args, to_exprs(args), k);
        mk_c(c)->save_ast_trail(a);
        check_sorts(c, a);
        RETURN_Z3(of_ast(a));
        Z3_CATCH_RETURN(0);
    }


    Z3_ast Z3_API Z3_mk_pble(Z3_context c, unsigned num_args, 
                             Z3_ast const args[], int coeffs[],
                             int k) {
        Z3_TRY;
        LOG_Z3_mk_pble(c, num_args, args, coeffs, k);
        RESET_ERROR_CODE();
        card_util util(mk_c(c)->m());
        ast* a = util.mk_le(num_args, coeffs, to_exprs(args), k);
        mk_c(c)->save_ast_trail(a);
        check_sorts(c, a);
        RETURN_Z3(of_ast(a));
        Z3_CATCH_RETURN(0);
    }


};
