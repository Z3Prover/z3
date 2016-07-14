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
#include"api_ast_vector.h"
#include"algebraic_numbers.h"
#include"expr2polynomial.h"
#include"cancel_eh.h"
#include"scoped_timer.h"


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

extern "C" {

    bool Z3_algebraic_is_value_core(Z3_context c, Z3_ast a) {
        api::context * _c = mk_c(c);
        return 
            is_expr(a) && 
            (_c->autil().is_numeral(to_expr(a)) || 
             _c->autil().is_irrational_algebraic_numeral(to_expr(a)));
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
        mk_c(c)->save_ast_trail(r);                                     \
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
        mk_c(c)->save_ast_trail(r);
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
        mk_c(c)->save_ast_trail(r);
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

    static bool to_anum_vector(Z3_context c, unsigned n, Z3_ast a[], scoped_anum_vector & as) {
        algebraic_numbers::manager & _am = am(c);
        scoped_anum tmp(_am);
        for (unsigned i = 0; i < n; i++) {
            if (is_rational(c, a[i])) {
                _am.set(tmp, get_rational(c, a[i]).to_mpq());       
                as.push_back(tmp);
            }
            else if (is_irrational(c, a[i])) {
                as.push_back(get_irrational(c, a[i]));
            }
            else {
                return false;
            }
        }
        return true;
    }

    class vector_var2anum : public polynomial::var2anum {
        scoped_anum_vector const & m_as;
    public:
        vector_var2anum(scoped_anum_vector & as):m_as(as) {}
        virtual ~vector_var2anum() {}
        virtual algebraic_numbers::manager & m() const { return m_as.m(); }
        virtual bool contains(polynomial::var x) const { return static_cast<unsigned>(x) < m_as.size(); }
        virtual algebraic_numbers::anum const & operator()(polynomial::var x) const { return m_as.get(x); }
    };

    Z3_ast_vector Z3_API Z3_algebraic_roots(Z3_context c, Z3_ast p, unsigned n, Z3_ast a[]) {
        Z3_TRY;
        LOG_Z3_algebraic_roots(c, p, n, a);
        RESET_ERROR_CODE();
        polynomial::manager & pm = mk_c(c)->pm();
        polynomial_ref _p(pm);
        polynomial::scoped_numeral d(pm.m());
        expr2polynomial converter(mk_c(c)->m(), pm, 0, true);
        if (!converter.to_polynomial(to_expr(p), _p, d) ||
            static_cast<unsigned>(max_var(_p)) >= n + 1) {
            SET_ERROR_CODE(Z3_INVALID_ARG);
            return 0;
        }
        algebraic_numbers::manager & _am = am(c);
        scoped_anum_vector as(_am);
        if (!to_anum_vector(c, n, a, as)) {
            SET_ERROR_CODE(Z3_INVALID_ARG);
            return 0;
        }
        scoped_anum_vector roots(_am);
        {
            cancel_eh<reslimit> eh(mk_c(c)->m().limit());
            api::context::set_interruptable si(*(mk_c(c)), eh);
            scoped_timer timer(mk_c(c)->params().m_timeout, &eh);
            vector_var2anum v2a(as);
            _am.isolate_roots(_p, v2a, roots);
        }
        Z3_ast_vector_ref* result = alloc(Z3_ast_vector_ref, *mk_c(c), mk_c(c)->m());
        mk_c(c)->save_object(result);
        for (unsigned i = 0; i < roots.size(); i++) {
            result->m_ast_vector.push_back(au(c).mk_numeral(roots.get(i), false));
        }
        RETURN_Z3(of_ast_vector(result));
        Z3_CATCH_RETURN(0);
    }

    int Z3_API Z3_algebraic_eval(Z3_context c, Z3_ast p, unsigned n, Z3_ast a[]) {
        Z3_TRY;
        LOG_Z3_algebraic_eval(c, p, n, a);
        RESET_ERROR_CODE();
        polynomial::manager & pm = mk_c(c)->pm();
        polynomial_ref _p(pm);
        polynomial::scoped_numeral d(pm.m());
        expr2polynomial converter(mk_c(c)->m(), pm, 0, true);
        if (!converter.to_polynomial(to_expr(p), _p, d) ||
            static_cast<unsigned>(max_var(_p)) >= n) {
            SET_ERROR_CODE(Z3_INVALID_ARG);
            return 0;
        }
        algebraic_numbers::manager & _am = am(c);
        scoped_anum_vector as(_am);
        if (!to_anum_vector(c, n, a, as)) {
            SET_ERROR_CODE(Z3_INVALID_ARG);
            return 0;
        }
        {
            cancel_eh<reslimit> eh(mk_c(c)->m().limit());
            api::context::set_interruptable si(*(mk_c(c)), eh);
            scoped_timer timer(mk_c(c)->params().m_timeout, &eh);
            vector_var2anum v2a(as);
            int r = _am.eval_sign_at(_p, v2a);
            if (r > 0) return 1;
            else if (r < 0) return -1;
            else return 0;
        }
        Z3_CATCH_RETURN(0);
    }

};
