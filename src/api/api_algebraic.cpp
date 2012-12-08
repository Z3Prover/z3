/*++
Copyright (c) 2012 Microsoft Corporation

Module Name:

    api_algebraic.cpp

Abstract:

    Additional APIs for handling Z3 algebraic numbers encoded as 
    Z3_ASTs

Author:

    Leonardo de Moura (leonardo) 2012-12-07

Notes:
    
--*/
#include<iostream>
#include"z3.h"
#include"api_log_macros.h"
#include"api_context.h"

extern "C" {

    Z3_bool Z3_API Z3_algebraic_is_value(Z3_context c, Z3_ast a) {
        Z3_TRY;
        LOG_Z3_algebraic_is_value(c, a);
        RESET_ERROR_CODE();
        // TODO
        return Z3_FALSE;
        Z3_CATCH_RETURN(Z3_FALSE);
    }

    Z3_bool Z3_API Z3_algebraic_is_pos(Z3_context c, Z3_ast a) {
        Z3_TRY;
        LOG_Z3_algebraic_is_pos(c, a);
        RESET_ERROR_CODE();
        // TODO
        return Z3_FALSE;
        Z3_CATCH_RETURN(Z3_FALSE);
    }

    Z3_bool Z3_API Z3_algebraic_is_neg(Z3_context c, Z3_ast a) {
        Z3_TRY;
        LOG_Z3_algebraic_is_neg(c, a);
        RESET_ERROR_CODE();
        // TODO
        return Z3_FALSE;
        Z3_CATCH_RETURN(Z3_FALSE);
    }

    Z3_bool Z3_API Z3_algebraic_is_zero(Z3_context c, Z3_ast a) {
        Z3_TRY;
        LOG_Z3_algebraic_is_zero(c, a);
        RESET_ERROR_CODE();
        // TODO
        return Z3_FALSE;
        Z3_CATCH_RETURN(Z3_FALSE);
    }

    int Z3_API Z3_algebraic_sign(Z3_context c, Z3_ast a) {
        Z3_TRY;
        LOG_Z3_algebraic_sign(c, a);
        RESET_ERROR_CODE();
        // TODO
        return 0;
        Z3_CATCH_RETURN(0);
    }

    Z3_ast Z3_API Z3_algebraic_add(Z3_context c, Z3_ast a, Z3_ast b) {
        Z3_TRY;
        LOG_Z3_algebraic_add(c, a, b);
        RESET_ERROR_CODE();
        // TODO
        return 0;
        Z3_CATCH_RETURN(0);
    }

    Z3_ast Z3_API Z3_algebraic_sub(Z3_context c, Z3_ast a, Z3_ast b) {
        Z3_TRY;
        LOG_Z3_algebraic_sub(c, a, b);
        RESET_ERROR_CODE();
        // TODO
        return 0;
        Z3_CATCH_RETURN(0);
    }

    Z3_ast Z3_API Z3_algebraic_mul(Z3_context c, Z3_ast a, Z3_ast b) {
        Z3_TRY;
        LOG_Z3_algebraic_mul(c, a, b);
        RESET_ERROR_CODE();
        // TODO
        return 0;
        Z3_CATCH_RETURN(0);
    }

    Z3_ast Z3_API Z3_algebraic_div(Z3_context c, Z3_ast a, Z3_ast b) {
        Z3_TRY;
        LOG_Z3_algebraic_div(c, a, b);
        RESET_ERROR_CODE();
        // TODO
        return 0;
        Z3_CATCH_RETURN(0);
    }

    Z3_ast Z3_API Z3_algebraic_root(Z3_context c, Z3_ast a, unsigned k) {
        Z3_TRY;
        LOG_Z3_algebraic_root(c, a, k);
        RESET_ERROR_CODE();
        // TODO
        return 0;
        Z3_CATCH_RETURN(0);
    }

    Z3_ast Z3_API Z3_algebraic_power(Z3_context c, Z3_ast a, unsigned k) {
        Z3_TRY;
        LOG_Z3_algebraic_power(c, a, k);
        RESET_ERROR_CODE();
        // TODO
        return 0;
        Z3_CATCH_RETURN(0);
    }

    Z3_bool Z3_API Z3_algebraic_lt(Z3_context c, Z3_ast a, Z3_ast b) {
        Z3_TRY;
        LOG_Z3_algebraic_lt(c, a, b);
        RESET_ERROR_CODE();
        // TODO
        return Z3_FALSE;
        Z3_CATCH_RETURN(Z3_FALSE);
    }

    Z3_bool Z3_API Z3_algebraic_gt(Z3_context c, Z3_ast a, Z3_ast b) {
        Z3_TRY;
        LOG_Z3_algebraic_gt(c, a, b);
        RESET_ERROR_CODE();
        // TODO
        return Z3_FALSE;
        Z3_CATCH_RETURN(Z3_FALSE);
    }

    Z3_bool Z3_API Z3_algebraic_le(Z3_context c, Z3_ast a, Z3_ast b) {
        Z3_TRY;
        LOG_Z3_algebraic_le(c, a, b);
        RESET_ERROR_CODE();
        // TODO
        return Z3_FALSE;
        Z3_CATCH_RETURN(Z3_FALSE);
    }

    Z3_bool Z3_API Z3_algebraic_ge(Z3_context c, Z3_ast a, Z3_ast b) {
        Z3_TRY;
        LOG_Z3_algebraic_ge(c, a, b);
        RESET_ERROR_CODE();
        // TODO
        return Z3_FALSE;
        Z3_CATCH_RETURN(0);
    }

    Z3_bool Z3_API Z3_algebraic_eq(Z3_context c, Z3_ast a, Z3_ast b) {
        Z3_TRY;
        LOG_Z3_algebraic_eq(c, a, b);
        RESET_ERROR_CODE();
        // TODO
        return Z3_FALSE;
        Z3_CATCH_RETURN(0);
    }

    Z3_bool Z3_API Z3_algebraic_neq(Z3_context c, Z3_ast a, Z3_ast b) {
        Z3_TRY;
        LOG_Z3_algebraic_neq(c, a, b);
        RESET_ERROR_CODE();
        // TODO
        return Z3_FALSE;
        Z3_CATCH_RETURN(0);
    }

    Z3_ast_vector Z3_API Z3_algebraic_roots(Z3_context c, Z3_ast p, unsigned n, Z3_ast a[]) {
        Z3_TRY;
        LOG_Z3_algebraic_roots(c, p, n, a);
        RESET_ERROR_CODE();
        // TODO
        return 0;
        Z3_CATCH_RETURN(0);
    }

    int Z3_API Z3_algebraic_eval(Z3_context c, Z3_ast p, unsigned n, Z3_ast a[]) {
        Z3_TRY;
        LOG_Z3_algebraic_eval(c, p, n, a);
        RESET_ERROR_CODE();
        // TODO
        return 0;
        Z3_CATCH_RETURN(0);
    }

};
