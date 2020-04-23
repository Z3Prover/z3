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
#include "api/z3.h"
#include "api/api_log_macros.h"
#include "api/api_context.h"
#include "api/api_util.h"
#include "ast/pb_decl_plugin.h"

extern "C" {

    Z3_ast Z3_API Z3_mk_atmost(Z3_context c, unsigned num_args,
                               Z3_ast const args[], unsigned k) {
        Z3_TRY;
        LOG_Z3_mk_atmost(c, num_args, args, k);
        RESET_ERROR_CODE();
        parameter param(k);
        pb_util util(mk_c(c)->m());
        ast* a = util.mk_at_most_k(num_args, to_exprs(num_args, args), k);
        mk_c(c)->save_ast_trail(a);
        check_sorts(c, a);
        RETURN_Z3(of_ast(a));
        Z3_CATCH_RETURN(nullptr);
    }

    Z3_ast Z3_API Z3_mk_atleast(Z3_context c, unsigned num_args,
                                Z3_ast const args[], unsigned k) {
        Z3_TRY;
        LOG_Z3_mk_atmost(c, num_args, args, k);
        RESET_ERROR_CODE();
        parameter param(k);
        pb_util util(mk_c(c)->m());
        ast* a = util.mk_at_least_k(num_args, to_exprs(num_args, args), k);
        mk_c(c)->save_ast_trail(a);
        check_sorts(c, a);
        RETURN_Z3(of_ast(a));
        Z3_CATCH_RETURN(nullptr);
    }

    Z3_ast Z3_API Z3_mk_pble(Z3_context c, unsigned num_args,
                             Z3_ast const args[], int const _coeffs[],
                             int k) {
        Z3_TRY;
        LOG_Z3_mk_pble(c, num_args, args, _coeffs, k);
        RESET_ERROR_CODE();
        pb_util util(mk_c(c)->m());
        vector<rational> coeffs;
        for (unsigned i = 0; i < num_args; ++i) {
            coeffs.push_back(rational(_coeffs[i]));
        }
        ast* a = util.mk_le(num_args, coeffs.c_ptr(), to_exprs(num_args, args), rational(k));
        mk_c(c)->save_ast_trail(a);
        check_sorts(c, a);
        RETURN_Z3(of_ast(a));
        Z3_CATCH_RETURN(nullptr);
    }

    Z3_ast Z3_API Z3_mk_pbge(Z3_context c, unsigned num_args,
                             Z3_ast const args[], int const _coeffs[],
                             int k) {
        Z3_TRY;
        LOG_Z3_mk_pble(c, num_args, args, _coeffs, k);
        RESET_ERROR_CODE();
        pb_util util(mk_c(c)->m());
        vector<rational> coeffs;
        for (unsigned i = 0; i < num_args; ++i) {
            coeffs.push_back(rational(_coeffs[i]));
        }
        ast* a = util.mk_ge(num_args, coeffs.c_ptr(), to_exprs(num_args, args), rational(k));
        mk_c(c)->save_ast_trail(a);
        check_sorts(c, a);
        RETURN_Z3(of_ast(a));
        Z3_CATCH_RETURN(nullptr);
    }

    Z3_ast Z3_API Z3_mk_pbeq(Z3_context c, unsigned num_args,
                             Z3_ast const args[], int const _coeffs[],
                             int k) {
        Z3_TRY;
        LOG_Z3_mk_pble(c, num_args, args, _coeffs, k);
        RESET_ERROR_CODE();
        pb_util util(mk_c(c)->m());
        vector<rational> coeffs;
        for (unsigned i = 0; i < num_args; ++i) {
            coeffs.push_back(rational(_coeffs[i]));
        }
        ast* a = util.mk_eq(num_args, coeffs.c_ptr(), to_exprs(num_args, args), rational(k));
        mk_c(c)->save_ast_trail(a);
        check_sorts(c, a);
        RETURN_Z3(of_ast(a));
        Z3_CATCH_RETURN(nullptr);
    }


};
