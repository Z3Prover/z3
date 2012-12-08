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
#include"algebraic_numbers.h"

extern "C" {

    bool Z3_algebraic_is_value_core(Z3_context c, Z3_ast a) {
        api::context * _c = mk_c(c);
        return 
            is_expr(a) && 
            (_c->autil().is_numeral(to_expr(a)) || 
             _c->autil().is_irrational_algebraic_numeral(to_expr(a)));
    }

#define CHECK_IS_ALGEBRAIC(ARG, RET) {          \
    if (!Z3_algebraic_is_value_core(c, ARG)) {  \
        SET_ERROR_CODE(Z3_INVALID_ARG);         \
        return RET;                             \
    }                                           \
}

#define CHECK_IS_ALGEBRAIC_X(ARG, RET) {        \
    if (!Z3_algebraic_is_value_core(c, ARG)) {  \
        SET_ERROR_CODE(Z3_INVALID_ARG);         \
        RETURN_Z3(RET);                         \
    }                                           \
}

    static arith_util & au(Z3_context c) {
        return mk_c(c)->autil();
    }

    static algebraic_numbers::manager & am(Z3_context c) {
        return au(c).am();
    }

    static bool is_rational(Z3_context c, Z3_ast a) {
        return au(c).is_numeral(to_expr(a));
    }

    static bool is_irrational(Z3_context c, Z3_ast a) {
        return au(c).is_irrational_algebraic_numeral(to_expr(a));
    }

    static rational get_rational(Z3_context c, Z3_ast a) {
        SASSERT(is_rational(c, a));
        rational r;
        VERIFY(au(c).is_numeral(to_expr(a), r));
        return r;
    }
    
    static algebraic_numbers::anum const & get_irrational(Z3_context c, Z3_ast a) {
        SASSERT(is_irrational(c, a));
        return au(c).to_irrational_algebraic_numeral(to_expr(a));
    }

    Z3_bool Z3_API Z3_algebraic_is_value(Z3_context c, Z3_ast a) {
        Z3_TRY;
        LOG_Z3_algebraic_is_value(c, a);
        RESET_ERROR_CODE();
        return Z3_algebraic_is_value_core(c, a) ? Z3_TRUE : Z3_FALSE;
        Z3_CATCH_RETURN(Z3_FALSE);
    }

    Z3_bool Z3_API Z3_algebraic_is_pos(Z3_context c, Z3_ast a) {
        return Z3_algebraic_sign(c, a) > 0;
    }

    Z3_bool Z3_API Z3_algebraic_is_neg(Z3_context c, Z3_ast a) {
        return Z3_algebraic_sign(c, a) < 0;
    }

    Z3_bool Z3_API Z3_algebraic_is_zero(Z3_context c, Z3_ast a) {
        return Z3_algebraic_sign(c, a) == 0;
    }

    int Z3_API Z3_algebraic_sign(Z3_context c, Z3_ast a) {
        Z3_TRY;
        LOG_Z3_algebraic_sign(c, a);
        RESET_ERROR_CODE();
        CHECK_IS_ALGEBRAIC(a, 0);
        if (is_rational(c, a)) {
            rational v = get_rational(c, a);
            if (v.is_pos()) return 1;
            else if (v.is_neg()) return -1;
            else return 0;
        }
        else {
            algebraic_numbers::anum const & v = get_irrational(c, a);
            if (am(c).is_pos(v)) return 1;
            else if (am(c).is_neg(v)) return -1;
            else return 0;
        }
        Z3_CATCH_RETURN(0);
    }

#define BIN_OP(RAT_OP, IRAT_OP)                                         \
        algebraic_numbers::manager & _am = am(c);                       \
        ast * r = 0;                                                    \
        if (is_rational(c, a)) {                                        \
            rational av = get_rational(c, a);                           \
            if (is_rational(c, b)) {                                    \
                rational bv = get_rational(c, b);                       \
                r = au(c).mk_numeral(av RAT_OP bv, false);              \
            }                                                           \
            else {                                                      \
                algebraic_numbers::anum const & bv = get_irrational(c, b); \
                scoped_anum _av(_am);                                   \
                _am.set(_av, av.to_mpq());                              \
                scoped_anum _r(_am);                                    \
                _am.IRAT_OP(_av, bv, _r);                               \
                r = au(c).mk_numeral(_r, false);                        \
            }                                                           \
        }                                                               \
        else {                                                          \
            algebraic_numbers::anum const & av = get_irrational(c, a);  \
            if (is_rational(c, b)) {                                    \
                rational bv = get_rational(c, b);                       \
                scoped_anum _bv(_am);                                   \
                _am.set(_bv, bv.to_mpq());                              \
                scoped_anum _r(_am);                                    \
                _am.IRAT_OP(av, _bv, _r);                               \
                r = au(c).mk_numeral(_r, false);                        \
            }                                                           \
            else {                                                      \
                algebraic_numbers::anum const & bv = get_irrational(c, b); \
                scoped_anum _r(_am);                                    \
                _am.IRAT_OP(av, bv, _r);                                \
                r = au(c).mk_numeral(_r, false);                        \
            }                                                           \
        }                                                               \
        RETURN_Z3(of_ast(r));


    Z3_ast Z3_API Z3_algebraic_add(Z3_context c, Z3_ast a, Z3_ast b) {
        Z3_TRY;
        LOG_Z3_algebraic_add(c, a, b);
        RESET_ERROR_CODE();                                             
        CHECK_IS_ALGEBRAIC_X(a, 0);                                       
        CHECK_IS_ALGEBRAIC_X(b, 0);                                       
        BIN_OP(+,add);
        Z3_CATCH_RETURN(0);
    }

    Z3_ast Z3_API Z3_algebraic_sub(Z3_context c, Z3_ast a, Z3_ast b) {
        Z3_TRY;
        LOG_Z3_algebraic_sub(c, a, b);
        RESET_ERROR_CODE();                                             
        CHECK_IS_ALGEBRAIC_X(a, 0);                                       
        CHECK_IS_ALGEBRAIC_X(b, 0);                                       
        BIN_OP(-,sub);
        Z3_CATCH_RETURN(0);
    }

    Z3_ast Z3_API Z3_algebraic_mul(Z3_context c, Z3_ast a, Z3_ast b) {
        Z3_TRY;
        LOG_Z3_algebraic_mul(c, a, b);
        RESET_ERROR_CODE();                                             
        CHECK_IS_ALGEBRAIC_X(a, 0);                                       
        CHECK_IS_ALGEBRAIC_X(b, 0);                                       
        BIN_OP(*,mul);
        Z3_CATCH_RETURN(0);
    }

    Z3_ast Z3_API Z3_algebraic_div(Z3_context c, Z3_ast a, Z3_ast b) {
        Z3_TRY;
        LOG_Z3_algebraic_div(c, a, b);
        RESET_ERROR_CODE();
        CHECK_IS_ALGEBRAIC_X(a, 0);
        CHECK_IS_ALGEBRAIC_X(b, 0);
        if ((is_rational(c, b) && get_rational(c, b).is_zero()) ||
            (!is_rational(c, b) && am(c).is_zero(get_irrational(c, b)))) {
            SET_ERROR_CODE(Z3_INVALID_ARG);
            RETURN_Z3(0);
        }
        BIN_OP(/,div);
        Z3_CATCH_RETURN(0);
    }

    Z3_ast Z3_API Z3_algebraic_root(Z3_context c, Z3_ast a, unsigned k) {
        Z3_TRY;
        LOG_Z3_algebraic_root(c, a, k);
        RESET_ERROR_CODE();
        CHECK_IS_ALGEBRAIC_X(a, 0);
        if (k % 2 == 0) {
            if ((is_rational(c, a) && get_rational(c, a).is_neg()) ||
                (!is_rational(c, a) && am(c).is_neg(get_irrational(c, a)))) {
                SET_ERROR_CODE(Z3_INVALID_ARG);
                RETURN_Z3(0);
            }
        }
        algebraic_numbers::manager & _am = am(c);
        scoped_anum _r(_am);
        if (is_rational(c, a)) {
            scoped_anum av(_am);                                     
            _am.set(av, get_rational(c, a).to_mpq());   
            _am.root(av, k, _r);
        }
        else {
            algebraic_numbers::anum const & av = get_irrational(c, a);
            _am.root(av, k, _r);
        }
        expr * r = au(c).mk_numeral(_r, false);
        RETURN_Z3(of_ast(r));
        Z3_CATCH_RETURN(0);
    }

    Z3_ast Z3_API Z3_algebraic_power(Z3_context c, Z3_ast a, unsigned k) {
        Z3_TRY;
        LOG_Z3_algebraic_power(c, a, k);
        RESET_ERROR_CODE();
        CHECK_IS_ALGEBRAIC_X(a, 0);
        algebraic_numbers::manager & _am = am(c);
        scoped_anum _r(_am);
        if (is_rational(c, a)) {
            scoped_anum av(_am);                                     
            _am.set(av, get_rational(c, a).to_mpq());   
            _am.power(av, k, _r);
        }
        else {
            algebraic_numbers::anum const & av = get_irrational(c, a);
            _am.power(av, k, _r);
        }
        expr * r = au(c).mk_numeral(_r, false);
        RETURN_Z3(of_ast(r));
        Z3_CATCH_RETURN(0);
    }

#define BIN_PRED(RAT_PRED, IRAT_PRED)                                   \
        algebraic_numbers::manager & _am = am(c);                       \
        bool r;                                                         \
        if (is_rational(c, a)) {                                        \
            rational av = get_rational(c, a);                           \
            if (is_rational(c, b)) {                                    \
                rational bv = get_rational(c, b);                       \
                r = av RAT_PRED bv;                                     \
            }                                                           \
            else {                                                      \
                algebraic_numbers::anum const & bv = get_irrational(c, b); \
                scoped_anum _av(_am);                                   \
                _am.set(_av, av.to_mpq());                              \
                r = _am.IRAT_PRED(_av, bv);                             \
            }                                                           \
        }                                                               \
        else {                                                          \
            algebraic_numbers::anum const & av = get_irrational(c, a);  \
            if (is_rational(c, b)) {                                    \
                rational bv = get_rational(c, b);                       \
                scoped_anum _bv(_am);                                   \
                _am.set(_bv, bv.to_mpq());                              \
                r = _am.IRAT_PRED(av, _bv);                             \
            }                                                           \
            else {                                                      \
                algebraic_numbers::anum const & bv = get_irrational(c, b); \
                r = _am.IRAT_PRED(av, bv);                              \
            }                                                           \
        }                                                               \
        return r ? Z3_TRUE : Z3_FALSE;


    Z3_bool Z3_API Z3_algebraic_lt(Z3_context c, Z3_ast a, Z3_ast b) {
        Z3_TRY;
        LOG_Z3_algebraic_lt(c, a, b);
        RESET_ERROR_CODE();
        CHECK_IS_ALGEBRAIC(a, 0);
        CHECK_IS_ALGEBRAIC(b, 0);
        BIN_PRED(<,lt);
        Z3_CATCH_RETURN(Z3_FALSE);
    }

    Z3_bool Z3_API Z3_algebraic_gt(Z3_context c, Z3_ast a, Z3_ast b) {
        return Z3_algebraic_lt(c, b, a);
    }

    Z3_bool Z3_API Z3_algebraic_le(Z3_context c, Z3_ast a, Z3_ast b) {
        return !Z3_algebraic_lt(c, b, a);
    }

    Z3_bool Z3_API Z3_algebraic_ge(Z3_context c, Z3_ast a, Z3_ast b) {
        return !Z3_algebraic_lt(c, a, b);
    }

    Z3_bool Z3_API Z3_algebraic_eq(Z3_context c, Z3_ast a, Z3_ast b) {
        Z3_TRY;
        LOG_Z3_algebraic_eq(c, a, b);
        RESET_ERROR_CODE();
        CHECK_IS_ALGEBRAIC(a, 0);
        CHECK_IS_ALGEBRAIC(b, 0);
        BIN_PRED(==,eq);
        Z3_CATCH_RETURN(0);
    }

    Z3_bool Z3_API Z3_algebraic_neq(Z3_context c, Z3_ast a, Z3_ast b) {
        return !Z3_algebraic_eq(c, a, b);
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
