/*++
Copyright (c) 2012 Microsoft Corporation

Module Name:

    api_arith.cpp

Abstract:
    API for arith theory

Author:

    Leonardo de Moura (leonardo) 2012-02-29.

Revision History:

--*/
#include<iostream>
#include"z3.h"
#include"api_log_macros.h"
#include"api_context.h"
#include"api_util.h"
#include"arith_decl_plugin.h"
#include"algebraic_numbers.h"

#define MK_ARITH_OP(NAME, OP) MK_NARY(NAME, mk_c(c)->get_arith_fid(), OP, SKIP)
#define MK_BINARY_ARITH_OP(NAME, OP) MK_BINARY(NAME, mk_c(c)->get_arith_fid(), OP, SKIP)
#define MK_ARITH_PRED(NAME, OP) MK_BINARY(NAME, mk_c(c)->get_arith_fid(), OP, SKIP)

extern "C" {

    Z3_sort Z3_API Z3_mk_int_sort(Z3_context c) {
        Z3_TRY;
        LOG_Z3_mk_int_sort(c);
        RESET_ERROR_CODE();
        Z3_sort r = of_sort(mk_c(c)->m().mk_sort(mk_c(c)->get_arith_fid(), INT_SORT));
        RETURN_Z3(r);
        Z3_CATCH_RETURN(0);
    }
    
    Z3_sort Z3_API Z3_mk_real_sort(Z3_context c) {
        Z3_TRY;
        LOG_Z3_mk_real_sort(c);
        RESET_ERROR_CODE();
        Z3_sort r = of_sort(mk_c(c)->m().mk_sort(mk_c(c)->get_arith_fid(), REAL_SORT));
        RETURN_Z3(r);
        Z3_CATCH_RETURN(0);
    }

    Z3_ast Z3_API Z3_mk_real(Z3_context c, int num, int den) {
        Z3_TRY;
        LOG_Z3_mk_real(c, num, den);
        RESET_ERROR_CODE();          
        if (den == 0) {
            SET_ERROR_CODE(Z3_INVALID_ARG);
            RETURN_Z3(0);
        }
        sort* s = mk_c(c)->m().mk_sort(mk_c(c)->get_arith_fid(), REAL_SORT);
        ast* a = mk_c(c)->mk_numeral_core(rational(num, den), s);
        RETURN_Z3(of_ast(a));
        Z3_CATCH_RETURN(0);
    }
    
    MK_ARITH_OP(Z3_mk_add, OP_ADD);
    MK_ARITH_OP(Z3_mk_mul, OP_MUL);
    MK_BINARY_ARITH_OP(Z3_mk_power, OP_POWER);
    MK_BINARY_ARITH_OP(Z3_mk_mod, OP_MOD);
    MK_BINARY_ARITH_OP(Z3_mk_rem, OP_REM);

    Z3_ast Z3_API Z3_mk_div(Z3_context c, Z3_ast n1, Z3_ast n2) {
        Z3_TRY;
        LOG_Z3_mk_div(c, n1, n2);
        RESET_ERROR_CODE();                                                 
        decl_kind k = OP_IDIV;
        sort* ty = mk_c(c)->m().get_sort(to_expr(n1));
        sort* real_ty = mk_c(c)->m().mk_sort(mk_c(c)->get_arith_fid(), REAL_SORT);
        if (ty == real_ty) {
            k = OP_DIV;
        }
        expr * args[2] = { to_expr(n1), to_expr(n2) };                         
        ast* a = mk_c(c)->m().mk_app(mk_c(c)->get_arith_fid(), k, 0, 0, 2, args);       
        mk_c(c)->save_ast_trail(a);                                         
        check_sorts(c, a);                                                  
        RETURN_Z3(of_ast(a));
        Z3_CATCH_RETURN(0);
    }

    MK_ARITH_PRED(Z3_mk_lt,  OP_LT);
    MK_ARITH_PRED(Z3_mk_gt,  OP_GT);
    MK_ARITH_PRED(Z3_mk_le,  OP_LE);
    MK_ARITH_PRED(Z3_mk_ge,  OP_GE);
    MK_UNARY(Z3_mk_int2real, mk_c(c)->get_arith_fid(), OP_TO_REAL, SKIP);
    MK_UNARY(Z3_mk_real2int, mk_c(c)->get_arith_fid(), OP_TO_INT, SKIP);
    MK_UNARY(Z3_mk_is_int,   mk_c(c)->get_arith_fid(), OP_IS_INT, SKIP);

    Z3_ast Z3_API Z3_mk_sub(Z3_context c, unsigned num_args, Z3_ast const args[]) {
        Z3_TRY;
        LOG_Z3_mk_sub(c, num_args, args);
        RESET_ERROR_CODE();
        if (num_args == 0) {
            SET_ERROR_CODE(Z3_INVALID_ARG);
            RETURN_Z3(0);
        }
        expr* r = to_expr(args[0]);
        for (unsigned i = 1; i < num_args; ++i) {
            expr* args1[2] = { r, to_expr(args[i]) };
            r = mk_c(c)->m().mk_app(mk_c(c)->get_arith_fid(), OP_SUB, 0, 0, 2, args1);
            check_sorts(c, r);
        }
        mk_c(c)->save_ast_trail(r);
        RETURN_Z3(of_expr(r));
        Z3_CATCH_RETURN(0);
    }

    Z3_ast Z3_API Z3_mk_unary_minus(Z3_context c, Z3_ast n) {
        Z3_TRY;
        LOG_Z3_mk_unary_minus(c, n);
        RESET_ERROR_CODE();
        MK_UNARY_BODY(Z3_mk_unary_minus, mk_c(c)->get_arith_fid(), OP_UMINUS, SKIP);
        Z3_CATCH_RETURN(0);
    }

    Z3_bool Z3_API Z3_is_algebraic_number(Z3_context c, Z3_ast a) {
        Z3_TRY;
        LOG_Z3_is_algebraic_number(c, a);
        RESET_ERROR_CODE();
        expr * e = to_expr(a);
        return mk_c(c)->autil().is_irrational_algebraic_numeral(e);
        Z3_CATCH_RETURN(Z3_FALSE);
    }

    Z3_ast Z3_API Z3_get_algebraic_number_lower(Z3_context c, Z3_ast a, unsigned precision) {
        Z3_TRY;
        LOG_Z3_get_algebraic_number_lower(c, a, precision);
        RESET_ERROR_CODE();
        if (!Z3_is_algebraic_number(c, a)) {
            SET_ERROR_CODE(Z3_INVALID_ARG);
            RETURN_Z3(0);
        }
        expr * e = to_expr(a);
        algebraic_numbers::anum const & val = mk_c(c)->autil().to_irrational_algebraic_numeral(e);
        rational l;
        mk_c(c)->autil().am().get_lower(val, l, precision);
        expr * r = mk_c(c)->autil().mk_numeral(l, false);
        mk_c(c)->save_ast_trail(r);                                         
        RETURN_Z3(of_expr(r));
        Z3_CATCH_RETURN(0);
    }

    Z3_ast Z3_API Z3_get_algebraic_number_upper(Z3_context c, Z3_ast a, unsigned precision) {
        Z3_TRY;
        LOG_Z3_get_algebraic_number_upper(c, a, precision);
        RESET_ERROR_CODE();
        if (!Z3_is_algebraic_number(c, a)) {
            SET_ERROR_CODE(Z3_INVALID_ARG);
            RETURN_Z3(0);
        }
        expr * e = to_expr(a);
        algebraic_numbers::anum const & val = mk_c(c)->autil().to_irrational_algebraic_numeral(e);
        rational l;
        mk_c(c)->autil().am().get_upper(val, l, precision);
        expr * r = mk_c(c)->autil().mk_numeral(l, false);
        mk_c(c)->save_ast_trail(r);                                         
        RETURN_Z3(of_expr(r));
        Z3_CATCH_RETURN(0);
    }

    Z3_ast Z3_API Z3_get_numerator(Z3_context c, Z3_ast a) {
        Z3_TRY;
        LOG_Z3_get_numerator(c, a);
        RESET_ERROR_CODE();
        rational val;
        ast * _a = to_ast(a);
        if (!is_expr(_a) || !mk_c(c)->autil().is_numeral(to_expr(_a), val)) {
            SET_ERROR_CODE(Z3_INVALID_ARG);
            RETURN_Z3(0);
        }
        expr * r = mk_c(c)->autil().mk_numeral(numerator(val), true);
        mk_c(c)->save_ast_trail(r);                                         
        RETURN_Z3(of_expr(r));
        Z3_CATCH_RETURN(0);
    }

    Z3_ast Z3_API Z3_get_denominator(Z3_context c, Z3_ast a) {
        Z3_TRY;
        LOG_Z3_get_denominator(c, a);
        RESET_ERROR_CODE();
        rational val;
        ast * _a = to_ast(a);
        if (!is_expr(_a) || !mk_c(c)->autil().is_numeral(to_expr(_a), val)) {
            SET_ERROR_CODE(Z3_INVALID_ARG);
            RETURN_Z3(0);
        }
        expr * r = mk_c(c)->autil().mk_numeral(denominator(val), true);
        mk_c(c)->save_ast_trail(r);                                         
        RETURN_Z3(of_expr(r));
        Z3_CATCH_RETURN(0);
    }

};
