/*++
Copyright (c) 2012 Microsoft Corporation

Module Name:

    api_bv.cpp

Abstract:
    API for bv theory

Author:

    Leonardo de Moura (leonardo) 2012-02-29.

Revision History:

--*/
#include<iostream>
#include"z3.h"
#include"api_log_macros.h"
#include"api_context.h"
#include"api_util.h"
#include"bv_decl_plugin.h"

extern "C" {

    Z3_sort Z3_API Z3_mk_bv_sort(Z3_context c, unsigned sz) {
        Z3_TRY;
        LOG_Z3_mk_bv_sort(c, sz);
        RESET_ERROR_CODE(); 
        if (sz == 0) {
            SET_ERROR_CODE(Z3_INVALID_ARG);
        }
        parameter p(sz);
        Z3_sort r = of_sort(mk_c(c)->m().mk_sort(mk_c(c)->get_bv_fid(), BV_SORT, 1, &p));
        RETURN_Z3(r);
        Z3_CATCH_RETURN(0);
    }

#define MK_BV_UNARY(NAME, OP) MK_UNARY(NAME, mk_c(c)->get_bv_fid(), OP, SKIP)
#define MK_BV_BINARY(NAME, OP) MK_BINARY(NAME, mk_c(c)->get_bv_fid(), OP, SKIP)
    
    MK_BV_UNARY(Z3_mk_bvnot, OP_BNOT);
    MK_BV_UNARY(Z3_mk_bvredand, OP_BREDAND);
    MK_BV_UNARY(Z3_mk_bvredor, OP_BREDOR);
    MK_BV_BINARY(Z3_mk_bvand, OP_BAND);
    MK_BV_BINARY(Z3_mk_bvor, OP_BOR);
    MK_BV_BINARY(Z3_mk_bvxor, OP_BXOR);
    MK_BV_BINARY(Z3_mk_bvnand, OP_BNAND);
    MK_BV_BINARY(Z3_mk_bvnor, OP_BNOR);
    MK_BV_BINARY(Z3_mk_bvxnor, OP_BXNOR);
    MK_BV_BINARY(Z3_mk_bvadd, OP_BADD);
    MK_BV_BINARY(Z3_mk_bvmul, OP_BMUL);
    MK_BV_BINARY(Z3_mk_bvudiv, OP_BUDIV);
    MK_BV_BINARY(Z3_mk_bvsdiv, OP_BSDIV);
    MK_BV_BINARY(Z3_mk_bvurem, OP_BUREM);
    MK_BV_BINARY(Z3_mk_bvsrem, OP_BSREM);
    MK_BV_BINARY(Z3_mk_bvsmod, OP_BSMOD);
    MK_BV_BINARY(Z3_mk_bvule, OP_ULEQ);
    MK_BV_BINARY(Z3_mk_bvsle, OP_SLEQ);
    MK_BV_BINARY(Z3_mk_bvuge, OP_UGEQ);
    MK_BV_BINARY(Z3_mk_bvsge, OP_SGEQ);
    MK_BV_BINARY(Z3_mk_bvult, OP_ULT);
    MK_BV_BINARY(Z3_mk_bvslt, OP_SLT);
    MK_BV_BINARY(Z3_mk_bvugt, OP_UGT);
    MK_BV_BINARY(Z3_mk_bvsgt, OP_SGT);
    MK_BV_BINARY(Z3_mk_concat, OP_CONCAT);
    MK_BV_BINARY(Z3_mk_bvshl, OP_BSHL);
    MK_BV_BINARY(Z3_mk_bvlshr, OP_BLSHR);
    MK_BV_BINARY(Z3_mk_bvashr, OP_BASHR);
    MK_BV_BINARY(Z3_mk_ext_rotate_left, OP_EXT_ROTATE_LEFT);
    MK_BV_BINARY(Z3_mk_ext_rotate_right, OP_EXT_ROTATE_RIGHT);

    Z3_ast mk_extract_core(Z3_context c, unsigned high, unsigned low, Z3_ast n) {
        expr * _n = to_expr(n);
        parameter params[2] = { parameter(high), parameter(low) };
        expr * a = mk_c(c)->m().mk_app(mk_c(c)->get_bv_fid(), OP_EXTRACT, 2, params, 1, &_n);
        mk_c(c)->save_ast_trail(a);  
        check_sorts(c, a);
        return of_ast(a);
    }
    
    Z3_ast Z3_API Z3_mk_extract(Z3_context c, unsigned high, unsigned low, Z3_ast n) {
        Z3_TRY;
        LOG_Z3_mk_extract(c, high, low, n);
        RESET_ERROR_CODE();
        Z3_ast r = mk_extract_core(c, high, low, n);
        RETURN_Z3(r);
        Z3_CATCH_RETURN(0);
    }
    
#define MK_BV_PUNARY(NAME, OP)                                          \
Z3_ast Z3_API NAME(Z3_context c, unsigned i, Z3_ast n) {                \
    Z3_TRY;                                                             \
    LOG_ ## NAME(c, i, n);                                              \
    RESET_ERROR_CODE();                                                 \
    expr * _n = to_expr(n);                                             \
    parameter p(i);                                                     \
    ast* a = mk_c(c)->m().mk_app(mk_c(c)->get_bv_fid(), OP, 1, &p, 1, &_n); \
    mk_c(c)->save_ast_trail(a);                                         \
    check_sorts(c, a);                                                  \
    RETURN_Z3(of_ast(a));                                               \
    Z3_CATCH_RETURN(0);                                                 \
}

    MK_BV_PUNARY(Z3_mk_sign_ext, OP_SIGN_EXT);
    MK_BV_PUNARY(Z3_mk_zero_ext, OP_ZERO_EXT);
    MK_BV_PUNARY(Z3_mk_repeat,   OP_REPEAT);
    MK_BV_PUNARY(Z3_mk_rotate_left, OP_ROTATE_LEFT);
    MK_BV_PUNARY(Z3_mk_rotate_right, OP_ROTATE_RIGHT);
    MK_BV_PUNARY(Z3_mk_int2bv, OP_INT2BV);

    Z3_ast Z3_API Z3_mk_bv2int(Z3_context c, Z3_ast n, Z3_bool is_signed) {
        Z3_TRY;
        LOG_Z3_mk_bv2int(c, n, is_signed);
        RESET_ERROR_CODE();                                                         
        Z3_sort int_s = Z3_mk_int_sort(c);
        if (is_signed) {
            Z3_ast r = Z3_mk_bv2int(c, n, false);
            Z3_inc_ref(c, r);
            Z3_sort s = Z3_get_sort(c, n);
            unsigned sz = Z3_get_bv_sort_size(c, s);
            rational max_bound = power(rational(2), sz);
            Z3_ast bound = Z3_mk_numeral(c, max_bound.to_string().c_str(), int_s);
            Z3_inc_ref(c, bound);
            Z3_ast zero = Z3_mk_int(c, 0, s);
            Z3_inc_ref(c, zero);
            Z3_ast pred = Z3_mk_bvslt(c, n, zero);        
            Z3_inc_ref(c, pred);
            // if n <_sigend 0 then r - s^sz else r
            Z3_ast args[2] = { r, bound };
            Z3_ast sub = Z3_mk_sub(c, 2, args);
            Z3_inc_ref(c, sub);
            Z3_ast res = Z3_mk_ite(c, pred, sub, r);
            Z3_dec_ref(c, bound);
            Z3_dec_ref(c, pred);
            Z3_dec_ref(c, sub);
            Z3_dec_ref(c, zero);
            Z3_dec_ref(c, r);
            RETURN_Z3(res);
        }
        else {
            expr * _n = to_expr(n);                                                     
            parameter p(to_sort(int_s));                                                             
            ast* a = mk_c(c)->m().mk_app(mk_c(c)->get_bv_fid(), OP_BV2INT, 1, &p, 1, &_n);   
            mk_c(c)->save_ast_trail(a);                                                 
            check_sorts(c, a);                                                          
            RETURN_Z3(of_ast(a)); 
        }
        Z3_CATCH_RETURN(0);
    }

    /**
       \brief \mlh mk_bvmsb c s \endmlh
       Create a bit-vector of sort \s with 1 in the most significant bit position.
       
       The sort \s must be a bit-vector sort.

       This function is a shorthand for <tt>shl(1, N-1)</tt>
       where <tt>N</tt> are the number of bits of \c s.
    */
    Z3_ast Z3_API Z3_mk_bvmsb(Z3_context c, Z3_sort s) {
        Z3_TRY;
        RESET_ERROR_CODE();
        // Not logging this one, since it is just syntax sugar.
        unsigned sz = Z3_get_bv_sort_size(c, s);
        if (sz == 0) {
            SET_ERROR_CODE(Z3_INVALID_ARG);
            return 0;
        }
        Z3_ast x = Z3_mk_int64(c, 1, s);
        Z3_inc_ref(c, x);
        Z3_ast y = Z3_mk_int64(c, sz - 1, s);
        Z3_inc_ref(c, y);
        Z3_ast result = Z3_mk_bvshl(c, x, y);
        Z3_dec_ref(c, x);
        Z3_dec_ref(c, y);
        return result;
        Z3_CATCH_RETURN(0);
    }

    Z3_ast Z3_mk_bvsmin(Z3_context c, Z3_sort s) {
        return Z3_mk_bvmsb(c, s);
    }

    Z3_ast Z3_mk_bvsmax(Z3_context c, Z3_sort s) {
        return Z3_mk_bvnot(c, Z3_mk_bvmsb(c, s));
    }

    Z3_ast Z3_mk_bvumax(Z3_context c, Z3_sort s) {
        return Z3_mk_int(c, -1, s);
    }

    Z3_ast Z3_API Z3_mk_bvadd_no_overflow(Z3_context c, Z3_ast t1, Z3_ast t2, Z3_bool is_signed) {
        Z3_TRY;
        RESET_ERROR_CODE();
        if (is_signed) {
            Z3_ast zero = Z3_mk_int(c, 0, Z3_get_sort(c, t1));
            Z3_inc_ref(c, zero);
            Z3_ast r = Z3_mk_bvadd(c, t1, t2);
            Z3_inc_ref(c, r);
            Z3_ast l1 = Z3_mk_bvslt(c, zero, t1);
            Z3_inc_ref(c, l1);
            Z3_ast l2 = Z3_mk_bvslt(c, zero, t2);
            Z3_inc_ref(c, l2);
            Z3_ast args[2] = { l1, l2 };
            Z3_ast args_pos = Z3_mk_and(c, 2, args);
            Z3_inc_ref(c, args_pos);
            Z3_ast result = Z3_mk_implies(c, args_pos, Z3_mk_bvslt(c, zero, r));
            Z3_dec_ref(c, r);
            Z3_dec_ref(c, l1);
            Z3_dec_ref(c, l2);
            Z3_dec_ref(c, args_pos);
            Z3_dec_ref(c, zero);
            return result;
        }
        else {
            unsigned sz = Z3_get_bv_sort_size(c, Z3_get_sort(c, t1));
            t1 = Z3_mk_zero_ext(c, 1, t1);
            Z3_inc_ref(c, t1);
            t2 = Z3_mk_zero_ext(c, 1, t2);
            Z3_inc_ref(c, t2);
            Z3_ast r = Z3_mk_bvadd(c, t1, t2);
            Z3_inc_ref(c, r);
            Z3_ast ex = Z3_mk_extract(c, sz, sz, r);
            Z3_inc_ref(c, ex);
            Z3_ast result = Z3_mk_eq(c, ex, Z3_mk_int(c, 0, Z3_mk_bv_sort(c, 1)));
            Z3_dec_ref(c, t1);
            Z3_dec_ref(c, t2);
            Z3_dec_ref(c, ex);
            Z3_dec_ref(c, r);
            return result;
        }
        Z3_CATCH_RETURN(0);
    }

    // only for signed machine integers
    Z3_ast Z3_API Z3_mk_bvadd_no_underflow(Z3_context c, Z3_ast t1, Z3_ast t2) {
        Z3_TRY;
        RESET_ERROR_CODE();
        Z3_ast zero = Z3_mk_int(c, 0, Z3_get_sort(c, t1));
        Z3_inc_ref(c, zero);
        Z3_ast r = Z3_mk_bvadd(c, t1, t2);
        Z3_inc_ref(c, r);
        Z3_ast l1 = Z3_mk_bvslt(c, t1, zero);
        Z3_inc_ref(c, l1);
        Z3_ast l2 = Z3_mk_bvslt(c, t2, zero);
        Z3_inc_ref(c, l2);
        Z3_ast args[2] = { l1, l2 };
        Z3_ast args_neg = Z3_mk_and(c, 2, args);
        Z3_inc_ref(c, args_neg);
        Z3_ast lt = Z3_mk_bvslt(c, r, zero);
        Z3_inc_ref(c, lt);
        Z3_ast result = Z3_mk_implies(c, args_neg, lt);
        Z3_dec_ref(c, lt);
        Z3_dec_ref(c, l1);
        Z3_dec_ref(c, l2);
        Z3_dec_ref(c, r);
        Z3_dec_ref(c, args_neg);
        Z3_dec_ref(c, zero);
        return result;
        Z3_CATCH_RETURN(0);
    }

    // only for signed machine integers
    Z3_ast Z3_API Z3_mk_bvsub_no_overflow(Z3_context c, Z3_ast t1, Z3_ast t2) {
        Z3_TRY;
        RESET_ERROR_CODE();
        Z3_ast minus_t2 = Z3_mk_bvneg(c, t2);
        Z3_inc_ref(c, minus_t2);
        Z3_sort s = Z3_get_sort(c, t2);
        Z3_ast min = Z3_mk_bvsmin(c, s);
        Z3_inc_ref(c, min);
        Z3_ast x = Z3_mk_eq(c, t2, min);
        Z3_inc_ref(c, x);
        Z3_ast zero = Z3_mk_int(c, 0, s);
        Z3_inc_ref(c, zero);
        Z3_ast y = Z3_mk_bvslt(c, t1, zero);
        Z3_inc_ref(c, y);
        Z3_ast z = Z3_mk_bvadd_no_overflow(c, t1, minus_t2, true);
        Z3_inc_ref(c, z);
        Z3_ast result = Z3_mk_ite(c, x, y, z);
        mk_c(c)->save_ast_trail(to_app(result));
        Z3_dec_ref(c, minus_t2);
        Z3_dec_ref(c, min);
        Z3_dec_ref(c, x);
        Z3_dec_ref(c, y);
        Z3_dec_ref(c, z);
        Z3_dec_ref(c, zero);
        return result;
        Z3_CATCH_RETURN(0);
    }

    Z3_ast Z3_API Z3_mk_bvsub_no_underflow(Z3_context c, Z3_ast t1, Z3_ast t2, Z3_bool is_signed) {
        Z3_TRY;
        RESET_ERROR_CODE();
        if (is_signed) {
            Z3_ast zero = Z3_mk_int(c, 0, Z3_get_sort(c, t1));
            Z3_inc_ref(c, zero);
            Z3_ast minus_t2 = Z3_mk_bvneg(c, t2);
            Z3_inc_ref(c, minus_t2);
            Z3_ast x = Z3_mk_bvslt(c, zero, t2);
            Z3_inc_ref(c, x);
            Z3_ast y = Z3_mk_bvadd_no_underflow(c, t1, minus_t2);
            Z3_inc_ref(c, y);
            Z3_ast result = Z3_mk_implies(c, x, y);
            Z3_dec_ref(c, zero);
            Z3_dec_ref(c, minus_t2);
            Z3_dec_ref(c, x);
            Z3_dec_ref(c, y);
            return result;
        }
        else {
            return Z3_mk_bvule(c, t2, t1);
        }
        Z3_CATCH_RETURN(0);
    }

    Z3_ast Z3_API Z3_mk_bvmul_no_overflow(Z3_context c, Z3_ast n1, Z3_ast n2, Z3_bool is_signed) {
        LOG_Z3_mk_bvmul_no_overflow(c, n1, n2, is_signed);
        RESET_ERROR_CODE();
        if (is_signed) {
            MK_BINARY_BODY(Z3_mk_bvmul_no_overflow, mk_c(c)->get_bv_fid(), OP_BSMUL_NO_OVFL, SKIP);
        }
        else {
            MK_BINARY_BODY(Z3_mk_bvmul_no_overflow, mk_c(c)->get_bv_fid(), OP_BUMUL_NO_OVFL, SKIP);
        }
    }

    // only for signed machine integers
    Z3_ast Z3_API Z3_mk_bvmul_no_underflow(Z3_context c, Z3_ast n1, Z3_ast n2) {
        LOG_Z3_mk_bvmul_no_underflow(c, n1, n2);
        MK_BINARY_BODY(Z3_mk_bvmul_no_underflow, mk_c(c)->get_bv_fid(), OP_BSMUL_NO_UDFL, SKIP);
    }

    // only for signed machine integers
    Z3_ast Z3_API Z3_mk_bvneg_no_overflow(Z3_context c, Z3_ast t) {
        Z3_TRY;
        RESET_ERROR_CODE();
        Z3_ast min = Z3_mk_bvsmin(c, Z3_get_sort(c, t));
        if (Z3_get_error_code(c) != Z3_OK) return 0;
        Z3_ast eq  = Z3_mk_eq(c, t, min);
        if (Z3_get_error_code(c) != Z3_OK) return 0;
        return Z3_mk_not(c, eq);
        Z3_CATCH_RETURN(0);
    }
    
    // only for signed machine integers
    Z3_ast Z3_API Z3_mk_bvsdiv_no_overflow(Z3_context c, Z3_ast t1, Z3_ast t2) {
        Z3_TRY;
        RESET_ERROR_CODE();
        Z3_sort s = Z3_get_sort(c, t1);
        Z3_ast min = Z3_mk_bvmsb(c, s);
        Z3_inc_ref(c, min);
        Z3_ast x = Z3_mk_eq(c, t1, min);
        Z3_inc_ref(c, x);
        Z3_ast y = Z3_mk_int(c, -1, s);
        Z3_inc_ref(c, y);
        Z3_ast z = Z3_mk_eq(c, t2, y);
        Z3_inc_ref(c, z);
        Z3_ast args[2] = { x, z };
        Z3_ast u = Z3_mk_and(c, 2, args);
        Z3_inc_ref(c, u);
        Z3_ast result = Z3_mk_not(c, u);
        Z3_dec_ref(c, min);
        Z3_dec_ref(c, x);
        Z3_dec_ref(c, y);
        Z3_dec_ref(c, z);
        Z3_dec_ref(c, u);
        return result;
        Z3_CATCH_RETURN(0);
    }
    
    Z3_ast Z3_API Z3_mk_bvsub(Z3_context c, Z3_ast n1, Z3_ast n2) {
        Z3_TRY;
        LOG_Z3_mk_bvsub(c, n1, n2);
        RESET_ERROR_CODE();
        MK_BINARY_BODY(Z3_mk_bvsub, mk_c(c)->get_bv_fid(), OP_BSUB, SKIP);
        Z3_CATCH_RETURN(0);
    }

    Z3_ast Z3_API Z3_mk_bvneg(Z3_context c, Z3_ast n) {
        Z3_TRY;
        LOG_Z3_mk_bvneg(c, n);
        RESET_ERROR_CODE();
        MK_UNARY_BODY(Z3_mk_bvneg, mk_c(c)->get_bv_fid(), OP_BNEG, SKIP);
        Z3_CATCH_RETURN(0);
    }

    unsigned Z3_API Z3_get_bv_sort_size(Z3_context c, Z3_sort t) {
        Z3_TRY;
        LOG_Z3_get_bv_sort_size(c, t);
        RESET_ERROR_CODE(); 
        CHECK_VALID_AST(t, 0);
        if (to_sort(t)->get_family_id() == mk_c(c)->get_bv_fid() && to_sort(t)->get_decl_kind() == BV_SORT) {
            return to_sort(t)->get_parameter(0).get_int();
        }
        SET_ERROR_CODE(Z3_INVALID_ARG);
        return 0;
        Z3_CATCH_RETURN(0);
    }
    
};
