/*++
Copyright (c) 2013 Microsoft Corporation

Module Name:

    api_rcf.cpp

Abstract:

    Additional APIs for handling elements of the Z3 real closed field that contains:
       - transcendental extensions
       - infinitesimal extensions
       - algebraic extensions

Author:

    Leonardo de Moura (leonardo) 2012-01-05

Notes:
    
--*/
#include<iostream>
#include"z3.h"
#include"api_log_macros.h"
#include"api_context.h"
#include"api_rcf.h"

extern "C" {

    void Z3_API Z3_rcf_inc_ref(Z3_context c, Z3_rcf_num a) {
        Z3_TRY;
        LOG_Z3_rcf_inc_ref(c, a);
        RESET_ERROR_CODE();
        to_rcf_num(a)->inc_ref();
        Z3_CATCH;
    }

    void Z3_API Z3_rcf_dec_ref(Z3_context c, Z3_rcf_num a) {
        Z3_TRY;
        LOG_Z3_rcf_dec_ref(c, a);
        RESET_ERROR_CODE();
        if (to_rcf_num(a)->ref_count() == 1) {
            mk_c(c)->rcfm().del(to_rcnumeral(a));
        }
        to_rcf_num(a)->dec_ref();
        Z3_CATCH;
    }

    static rcmanager & rcfm(Z3_context c) {
        return mk_c(c)->rcfm();
    }

    static void reset_rcf_cancel(Z3_context c) {
        rcfm(c).reset_cancel();
    }
    
    static Z3_rcf_num mk_rcf_num(Z3_context c, rcnumeral & a) {
        Z3_rcf_num_ref * r = alloc(Z3_rcf_num_ref);
        rcfm(c).swap(r->m_num, a);
        mk_c(c)->save_object(r);
        return of_rcf_num(r);
    }
    
    Z3_rcf_num Z3_API Z3_rcf_mk_rational(Z3_context c, Z3_string val) {
        Z3_TRY;
        LOG_Z3_rcf_mk_rational(c, val);
        RESET_ERROR_CODE();
        reset_rcf_cancel(c);
        scoped_mpq q(rcfm(c).qm());
        rcfm(c).qm().set(q, val);
        scoped_rcnumeral r(rcfm(c));
        rcfm(c).set(r, q);
        RETURN_Z3(mk_rcf_num(c, r));
        Z3_CATCH_RETURN(0);
    }

    Z3_rcf_num Z3_API Z3_rcf_mk_small_int(Z3_context c, int val) {
        Z3_TRY;
        LOG_Z3_rcf_mk_small_int(c, val);
        RESET_ERROR_CODE();
        reset_rcf_cancel(c);
        scoped_rcnumeral r(rcfm(c));
        rcfm(c).set(r, val);
        RETURN_Z3(mk_rcf_num(c, r));
        Z3_CATCH_RETURN(0);
    }

    Z3_rcf_num Z3_API Z3_rcf_mk_pi(Z3_context c) {
        Z3_TRY;
        LOG_Z3_rcf_mk_pi(c);
        RESET_ERROR_CODE();
        reset_rcf_cancel(c);
        scoped_rcnumeral r(rcfm(c));
        rcfm(c).mk_pi(r);
        RETURN_Z3(mk_rcf_num(c, r));
        Z3_CATCH_RETURN(0);
    }

    Z3_rcf_num Z3_API Z3_rcf_mk_e(Z3_context c) {
        Z3_TRY;
        LOG_Z3_rcf_mk_e(c);
        RESET_ERROR_CODE();
        reset_rcf_cancel(c);
        scoped_rcnumeral r(rcfm(c));
        rcfm(c).mk_e(r);
        RETURN_Z3(mk_rcf_num(c, r));
        Z3_CATCH_RETURN(0);
    }

    Z3_rcf_num Z3_API Z3_rcf_mk_infinitesimal(Z3_context c, Z3_string name) {
        Z3_TRY;
        LOG_Z3_rcf_mk_infinitesimal(c, name);
        RESET_ERROR_CODE();
        reset_rcf_cancel(c);
        scoped_rcnumeral r(rcfm(c));
        rcfm(c).mk_infinitesimal(name, r);
        RETURN_Z3(mk_rcf_num(c, r));
        Z3_CATCH_RETURN(0);
    }

    Z3_rcf_num Z3_API Z3_rcf_add(Z3_context c, Z3_rcf_num a, Z3_rcf_num b) {
        Z3_TRY;
        LOG_Z3_rcf_add(c, a, b);
        RESET_ERROR_CODE();
        reset_rcf_cancel(c);
        scoped_rcnumeral r(rcfm(c));
        rcfm(c).add(to_rcnumeral(a), to_rcnumeral(b), r);
        RETURN_Z3(mk_rcf_num(c, r));
        Z3_CATCH_RETURN(0);
    }

    Z3_rcf_num Z3_API Z3_rcf_sub(Z3_context c, Z3_rcf_num a, Z3_rcf_num b) {
        Z3_TRY;
        LOG_Z3_rcf_sub(c, a, b);
        RESET_ERROR_CODE();
        reset_rcf_cancel(c);
        scoped_rcnumeral r(rcfm(c));
        rcfm(c).sub(to_rcnumeral(a), to_rcnumeral(b), r);
        RETURN_Z3(mk_rcf_num(c, r));
        Z3_CATCH_RETURN(0);
    }

    Z3_rcf_num Z3_API Z3_rcf_mul(Z3_context c, Z3_rcf_num a, Z3_rcf_num b) {
        Z3_TRY;
        LOG_Z3_rcf_mul(c, a, b);
        RESET_ERROR_CODE();
        reset_rcf_cancel(c);
        scoped_rcnumeral r(rcfm(c));
        rcfm(c).mul(to_rcnumeral(a), to_rcnumeral(b), r);
        RETURN_Z3(mk_rcf_num(c, r));
        Z3_CATCH_RETURN(0);
    }

    Z3_rcf_num Z3_API Z3_rcf_div(Z3_context c, Z3_rcf_num a, Z3_rcf_num b) {
        Z3_TRY;
        LOG_Z3_rcf_div(c, a, b);
        RESET_ERROR_CODE();
        reset_rcf_cancel(c);
        scoped_rcnumeral r(rcfm(c));
        rcfm(c).div(to_rcnumeral(a), to_rcnumeral(b), r);
        RETURN_Z3(mk_rcf_num(c, r));
        Z3_CATCH_RETURN(0);
    }
    
    Z3_rcf_num Z3_API Z3_rcf_neg(Z3_context c, Z3_rcf_num a) {
        Z3_TRY;
        LOG_Z3_rcf_neg(c, a);
        RESET_ERROR_CODE();
        reset_rcf_cancel(c);
        scoped_rcnumeral r(rcfm(c));
        rcfm(c).neg(to_rcnumeral(a), r);
        RETURN_Z3(mk_rcf_num(c, r));
        Z3_CATCH_RETURN(0);
    }

    Z3_rcf_num Z3_API Z3_rcf_inv(Z3_context c, Z3_rcf_num a) {
        Z3_TRY;
        LOG_Z3_rcf_inv(c, a);
        RESET_ERROR_CODE();
        reset_rcf_cancel(c);
        scoped_rcnumeral r(rcfm(c));
        rcfm(c).inv(to_rcnumeral(a), r);
        RETURN_Z3(mk_rcf_num(c, r));
        Z3_CATCH_RETURN(0);
    }

    Z3_bool Z3_API Z3_rcf_lt(Z3_context c, Z3_rcf_num a, Z3_rcf_num b) {
        Z3_TRY;
        LOG_Z3_rcf_lt(c, a, b);
        RESET_ERROR_CODE();
        reset_rcf_cancel(c);
        return rcfm(c).lt(to_rcnumeral(a), to_rcnumeral(b));
        Z3_CATCH_RETURN(Z3_FALSE);
    }

    Z3_bool Z3_API Z3_rcf_gt(Z3_context c, Z3_rcf_num a, Z3_rcf_num b) {
        Z3_TRY;
        LOG_Z3_rcf_gt(c, a, b);
        RESET_ERROR_CODE();
        reset_rcf_cancel(c);
        return rcfm(c).gt(to_rcnumeral(a), to_rcnumeral(b));
        Z3_CATCH_RETURN(Z3_FALSE);
    }

    Z3_bool Z3_API Z3_rcf_le(Z3_context c, Z3_rcf_num a, Z3_rcf_num b) {
        Z3_TRY;
        LOG_Z3_rcf_le(c, a, b);
        RESET_ERROR_CODE();
        reset_rcf_cancel(c);
        return rcfm(c).le(to_rcnumeral(a), to_rcnumeral(b));
        Z3_CATCH_RETURN(Z3_FALSE);
    }

    Z3_bool Z3_API Z3_rcf_ge(Z3_context c, Z3_rcf_num a, Z3_rcf_num b) {
        Z3_TRY;
        LOG_Z3_rcf_ge(c, a, b);
        RESET_ERROR_CODE();
        reset_rcf_cancel(c);
        return rcfm(c).ge(to_rcnumeral(a), to_rcnumeral(b));
        Z3_CATCH_RETURN(Z3_FALSE);
    }

    Z3_bool Z3_API Z3_rcf_eq(Z3_context c, Z3_rcf_num a, Z3_rcf_num b) {
        Z3_TRY;
        LOG_Z3_rcf_eq(c, a, b);
        RESET_ERROR_CODE();
        reset_rcf_cancel(c);
        return rcfm(c).eq(to_rcnumeral(a), to_rcnumeral(b));
        Z3_CATCH_RETURN(Z3_FALSE);
    }

    Z3_bool Z3_API Z3_rcf_neq(Z3_context c, Z3_rcf_num a, Z3_rcf_num b) {
        Z3_TRY;
        LOG_Z3_rcf_neq(c, a, b);
        RESET_ERROR_CODE();
        reset_rcf_cancel(c);
        return rcfm(c).eq(to_rcnumeral(a), to_rcnumeral(b));
        Z3_CATCH_RETURN(Z3_FALSE);
    }

    Z3_string Z3_API Z3_rcf_num_to_string(Z3_context c, Z3_rcf_num a) {
        Z3_TRY;
        LOG_Z3_rcf_num_to_string(c, a);
        RESET_ERROR_CODE();
        reset_rcf_cancel(c);
        std::ostringstream buffer;
        rcfm(c).display(buffer, to_rcnumeral(a));
        return mk_c(c)->mk_external_string(buffer.str());
        Z3_CATCH_RETURN("");
    }

    Z3_string Z3_API Z3_rcf_num_to_decimal_string(Z3_context c, Z3_rcf_num a, unsigned prec) {
        Z3_TRY;
        LOG_Z3_rcf_num_to_decimal_string(c, a, prec);
        RESET_ERROR_CODE();
        reset_rcf_cancel(c);
        std::ostringstream buffer;
        rcfm(c).display_decimal(buffer, to_rcnumeral(a), prec);
        return mk_c(c)->mk_external_string(buffer.str());
        Z3_CATCH_RETURN("");
    }

};
