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
#include "api/z3.h"
#include "api/api_log_macros.h"
#include "api/api_context.h"
#include "math/realclosure/realclosure.h"

static rcmanager & rcfm(Z3_context c) {
    return mk_c(c)->rcfm();
}

static void reset_rcf_cancel(Z3_context c) {
    // no-op
}

static Z3_rcf_num from_rcnumeral(rcnumeral a) {
    return reinterpret_cast<Z3_rcf_num>(a.data());
}

static rcnumeral to_rcnumeral(Z3_rcf_num a) {
    return rcnumeral::mk(a);
}

extern "C" {

    void Z3_API Z3_rcf_del(Z3_context c, Z3_rcf_num a) {
        Z3_TRY;
        LOG_Z3_rcf_del(c, a);
        RESET_ERROR_CODE();
        rcnumeral _a = to_rcnumeral(a);
        rcfm(c).del(_a);
        Z3_CATCH;
    }

    Z3_rcf_num Z3_API Z3_rcf_mk_rational(Z3_context c, Z3_string val) {
        Z3_TRY;
        LOG_Z3_rcf_mk_rational(c, val);
        RESET_ERROR_CODE();
        reset_rcf_cancel(c);
        scoped_mpq q(rcfm(c).qm());
        rcfm(c).qm().set(q, val);
        rcnumeral r;
        rcfm(c).set(r, q);
        RETURN_Z3(from_rcnumeral(r));
        Z3_CATCH_RETURN(nullptr);
    }

    Z3_rcf_num Z3_API Z3_rcf_mk_small_int(Z3_context c, int val) {
        Z3_TRY;
        LOG_Z3_rcf_mk_small_int(c, val);
        RESET_ERROR_CODE();
        reset_rcf_cancel(c);
        rcnumeral r;
        rcfm(c).set(r, val);
        RETURN_Z3(from_rcnumeral(r));
        Z3_CATCH_RETURN(nullptr);
    }

    Z3_rcf_num Z3_API Z3_rcf_mk_pi(Z3_context c) {
        Z3_TRY;
        LOG_Z3_rcf_mk_pi(c);
        RESET_ERROR_CODE();
        reset_rcf_cancel(c);
        rcnumeral r;
        rcfm(c).mk_pi(r);
        RETURN_Z3(from_rcnumeral(r));
        Z3_CATCH_RETURN(nullptr);
    }

    Z3_rcf_num Z3_API Z3_rcf_mk_e(Z3_context c) {
        Z3_TRY;
        LOG_Z3_rcf_mk_e(c);
        RESET_ERROR_CODE();
        reset_rcf_cancel(c);
        rcnumeral r;
        rcfm(c).mk_e(r);
        RETURN_Z3(from_rcnumeral(r));
        Z3_CATCH_RETURN(nullptr);
    }

    Z3_rcf_num Z3_API Z3_rcf_mk_infinitesimal(Z3_context c) {
        Z3_TRY;
        LOG_Z3_rcf_mk_infinitesimal(c);
        RESET_ERROR_CODE();
        reset_rcf_cancel(c);
        rcnumeral r;
        rcfm(c).mk_infinitesimal(r);
        RETURN_Z3(from_rcnumeral(r));
        Z3_CATCH_RETURN(nullptr);
    }

    unsigned Z3_API Z3_rcf_mk_roots(Z3_context c, unsigned n, Z3_rcf_num const a[], Z3_rcf_num roots[]) {
        Z3_TRY;
        LOG_Z3_rcf_mk_roots(c, n, a, roots);
        RESET_ERROR_CODE();
        reset_rcf_cancel(c);
        rcnumeral_vector av;
        unsigned rz = 0;
        for (unsigned i = 0; i < n; i++) {
            if (!rcfm(c).is_zero(to_rcnumeral(a[i])))
                rz = i + 1;
            av.push_back(to_rcnumeral(a[i]));
        }
        if (rz == 0) {
            // it is the zero polynomial
            SET_ERROR_CODE(Z3_INVALID_ARG, nullptr);
            return 0;
        }
        av.shrink(rz);
        rcnumeral_vector rs;
        rcfm(c).isolate_roots(av.size(), av.data(), rs);
        unsigned num_roots = rs.size();
        for (unsigned i = 0; i < num_roots; i++) {
            roots[i] = from_rcnumeral(rs[i]);
        }
        RETURN_Z3_rcf_mk_roots num_roots;
        Z3_CATCH_RETURN(0);
    }

    Z3_rcf_num Z3_API Z3_rcf_add(Z3_context c, Z3_rcf_num a, Z3_rcf_num b) {
        Z3_TRY;
        LOG_Z3_rcf_add(c, a, b);
        RESET_ERROR_CODE();
        reset_rcf_cancel(c);
        rcnumeral r;
        rcfm(c).add(to_rcnumeral(a), to_rcnumeral(b), r);
        RETURN_Z3(from_rcnumeral(r));
        Z3_CATCH_RETURN(nullptr);
    }

    Z3_rcf_num Z3_API Z3_rcf_sub(Z3_context c, Z3_rcf_num a, Z3_rcf_num b) {
        Z3_TRY;
        LOG_Z3_rcf_sub(c, a, b);
        RESET_ERROR_CODE();
        reset_rcf_cancel(c);
        rcnumeral r;
        rcfm(c).sub(to_rcnumeral(a), to_rcnumeral(b), r);
        RETURN_Z3(from_rcnumeral(r));
        Z3_CATCH_RETURN(nullptr);
    }

    Z3_rcf_num Z3_API Z3_rcf_mul(Z3_context c, Z3_rcf_num a, Z3_rcf_num b) {
        Z3_TRY;
        LOG_Z3_rcf_mul(c, a, b);
        RESET_ERROR_CODE();
        reset_rcf_cancel(c);
        rcnumeral r;
        rcfm(c).mul(to_rcnumeral(a), to_rcnumeral(b), r);
        RETURN_Z3(from_rcnumeral(r));
        Z3_CATCH_RETURN(nullptr);
    }

    Z3_rcf_num Z3_API Z3_rcf_div(Z3_context c, Z3_rcf_num a, Z3_rcf_num b) {
        Z3_TRY;
        LOG_Z3_rcf_div(c, a, b);
        RESET_ERROR_CODE();
        reset_rcf_cancel(c);
        rcnumeral r;
        rcfm(c).div(to_rcnumeral(a), to_rcnumeral(b), r);
        RETURN_Z3(from_rcnumeral(r));
        Z3_CATCH_RETURN(nullptr);
    }

    Z3_rcf_num Z3_API Z3_rcf_neg(Z3_context c, Z3_rcf_num a) {
        Z3_TRY;
        LOG_Z3_rcf_neg(c, a);
        RESET_ERROR_CODE();
        reset_rcf_cancel(c);
        rcnumeral r;
        rcfm(c).neg(to_rcnumeral(a), r);
        RETURN_Z3(from_rcnumeral(r));
        Z3_CATCH_RETURN(nullptr);
    }

    Z3_rcf_num Z3_API Z3_rcf_inv(Z3_context c, Z3_rcf_num a) {
        Z3_TRY;
        LOG_Z3_rcf_inv(c, a);
        RESET_ERROR_CODE();
        reset_rcf_cancel(c);
        rcnumeral r;
        rcfm(c).inv(to_rcnumeral(a), r);
        RETURN_Z3(from_rcnumeral(r));
        Z3_CATCH_RETURN(nullptr);
    }

    Z3_rcf_num Z3_API Z3_rcf_power(Z3_context c, Z3_rcf_num a, unsigned k) {
        Z3_TRY;
        LOG_Z3_rcf_power(c, a, k);
        RESET_ERROR_CODE();
        reset_rcf_cancel(c);
        rcnumeral r;
        rcfm(c).power(to_rcnumeral(a), k, r);
        RETURN_Z3(from_rcnumeral(r));
        Z3_CATCH_RETURN(nullptr);
    }

    bool Z3_API Z3_rcf_lt(Z3_context c, Z3_rcf_num a, Z3_rcf_num b) {
        Z3_TRY;
        LOG_Z3_rcf_lt(c, a, b);
        RESET_ERROR_CODE();
        reset_rcf_cancel(c);
        return rcfm(c).lt(to_rcnumeral(a), to_rcnumeral(b));
        Z3_CATCH_RETURN(false);
    }

    bool Z3_API Z3_rcf_gt(Z3_context c, Z3_rcf_num a, Z3_rcf_num b) {
        Z3_TRY;
        LOG_Z3_rcf_gt(c, a, b);
        RESET_ERROR_CODE();
        reset_rcf_cancel(c);
        return rcfm(c).gt(to_rcnumeral(a), to_rcnumeral(b));
        Z3_CATCH_RETURN(false);
    }

    bool Z3_API Z3_rcf_le(Z3_context c, Z3_rcf_num a, Z3_rcf_num b) {
        Z3_TRY;
        LOG_Z3_rcf_le(c, a, b);
        RESET_ERROR_CODE();
        reset_rcf_cancel(c);
        return rcfm(c).le(to_rcnumeral(a), to_rcnumeral(b));
        Z3_CATCH_RETURN(false);
    }

    bool Z3_API Z3_rcf_ge(Z3_context c, Z3_rcf_num a, Z3_rcf_num b) {
        Z3_TRY;
        LOG_Z3_rcf_ge(c, a, b);
        RESET_ERROR_CODE();
        reset_rcf_cancel(c);
        return rcfm(c).ge(to_rcnumeral(a), to_rcnumeral(b));
        Z3_CATCH_RETURN(false);
    }

    bool Z3_API Z3_rcf_eq(Z3_context c, Z3_rcf_num a, Z3_rcf_num b) {
        Z3_TRY;
        LOG_Z3_rcf_eq(c, a, b);
        RESET_ERROR_CODE();
        reset_rcf_cancel(c);
        return rcfm(c).eq(to_rcnumeral(a), to_rcnumeral(b));
        Z3_CATCH_RETURN(false);
    }

    bool Z3_API Z3_rcf_neq(Z3_context c, Z3_rcf_num a, Z3_rcf_num b) {
        Z3_TRY;
        LOG_Z3_rcf_neq(c, a, b);
        RESET_ERROR_CODE();
        reset_rcf_cancel(c);
        return rcfm(c).neq(to_rcnumeral(a), to_rcnumeral(b));
        Z3_CATCH_RETURN(false);
    }

    Z3_string Z3_API Z3_rcf_num_to_string(Z3_context c, Z3_rcf_num a, bool compact, bool html) {
        Z3_TRY;
        LOG_Z3_rcf_num_to_string(c, a, compact, html);
        RESET_ERROR_CODE();
        reset_rcf_cancel(c);
        std::ostringstream buffer;
        rcfm(c).display(buffer, to_rcnumeral(a), compact, html);
        return mk_c(c)->mk_external_string(std::move(buffer).str());
        Z3_CATCH_RETURN("");
    }

    Z3_string Z3_API Z3_rcf_num_to_decimal_string(Z3_context c, Z3_rcf_num a, unsigned prec) {
        Z3_TRY;
        LOG_Z3_rcf_num_to_decimal_string(c, a, prec);
        RESET_ERROR_CODE();
        reset_rcf_cancel(c);
        std::ostringstream buffer;
        rcfm(c).display_decimal(buffer, to_rcnumeral(a), prec);
        return mk_c(c)->mk_external_string(std::move(buffer).str());
        Z3_CATCH_RETURN("");
    }

    void Z3_API Z3_rcf_get_numerator_denominator(Z3_context c, Z3_rcf_num a, Z3_rcf_num * n, Z3_rcf_num * d) {
        Z3_TRY;
        LOG_Z3_rcf_get_numerator_denominator(c, a, n, d);
        RESET_ERROR_CODE();
        reset_rcf_cancel(c);
        rcnumeral _n, _d;
        rcfm(c).clean_denominators(to_rcnumeral(a), _n, _d);
        *n = from_rcnumeral(_n);
        *d = from_rcnumeral(_d);
        RETURN_Z3_rcf_get_numerator_denominator;
        Z3_CATCH;
    }

    bool Z3_API Z3_rcf_is_rational(Z3_context c, Z3_rcf_num a) {
        Z3_TRY;
        LOG_Z3_rcf_is_rational(c, a);
        RESET_ERROR_CODE();
        reset_rcf_cancel(c);
        return rcfm(c).is_rational(to_rcnumeral(a));
        Z3_CATCH_RETURN(false);
    }

    bool Z3_API Z3_rcf_is_algebraic(Z3_context c, Z3_rcf_num a) {
        Z3_TRY;
        LOG_Z3_rcf_is_algebraic(c, a);
        RESET_ERROR_CODE();
        reset_rcf_cancel(c);
        return rcfm(c).is_algebraic(to_rcnumeral(a));
        Z3_CATCH_RETURN(false);
    }

    bool Z3_API Z3_rcf_is_infinitesimal(Z3_context c, Z3_rcf_num a) {
        Z3_TRY;
        LOG_Z3_rcf_is_infinitesimal(c, a);
        RESET_ERROR_CODE();
        reset_rcf_cancel(c);
        return rcfm(c).is_infinitesimal(to_rcnumeral(a));
        Z3_CATCH_RETURN(false);
    }

    bool Z3_API Z3_rcf_is_transcendental(Z3_context c, Z3_rcf_num a) {
        Z3_TRY;
        LOG_Z3_rcf_is_transcendental(c, a);
        RESET_ERROR_CODE();
        reset_rcf_cancel(c);
        return rcfm(c).is_transcendental(to_rcnumeral(a));
        Z3_CATCH_RETURN(false);
    }

    unsigned Z3_API Z3_rcf_extension_index(Z3_context c, Z3_rcf_num a) {
        Z3_TRY;
        LOG_Z3_rcf_extension_index(c, a);
        RESET_ERROR_CODE();
        reset_rcf_cancel(c);
        return rcfm(c).extension_index(to_rcnumeral(a));
        Z3_CATCH_RETURN(false);
    }

    Z3_symbol Z3_API Z3_rcf_transcendental_name(Z3_context c, Z3_rcf_num a) {
        Z3_TRY;
        LOG_Z3_rcf_transcendental_name(c, a);
        RESET_ERROR_CODE();
        reset_rcf_cancel(c);
        return of_symbol(rcfm(c).transcendental_name(to_rcnumeral(a)));
        Z3_CATCH_RETURN(of_symbol(symbol::null));
    }

    Z3_symbol Z3_API Z3_rcf_infinitesimal_name(Z3_context c, Z3_rcf_num a) {
        Z3_TRY;
        LOG_Z3_rcf_infinitesimal_name(c, a);
        RESET_ERROR_CODE();
        reset_rcf_cancel(c);
        return of_symbol(rcfm(c).infinitesimal_name(to_rcnumeral(a)));
        Z3_CATCH_RETURN(of_symbol(symbol::null));
    }

    unsigned Z3_API Z3_rcf_num_coefficients(Z3_context c, Z3_rcf_num a)
    {
        Z3_TRY;
        LOG_Z3_rcf_num_coefficients(c, a);
        RESET_ERROR_CODE();
        reset_rcf_cancel(c);
        return rcfm(c).num_coefficients(to_rcnumeral(a));
        Z3_CATCH_RETURN(0);
    }

    Z3_rcf_num Z3_API Z3_rcf_coefficient(Z3_context c, Z3_rcf_num a, unsigned i)
    {
        Z3_TRY;
        LOG_Z3_rcf_coefficient(c, a, i);
        RESET_ERROR_CODE();
        reset_rcf_cancel(c);
        return from_rcnumeral(rcfm(c).get_coefficient(to_rcnumeral(a), i));
        Z3_CATCH_RETURN(nullptr);
    }

    int Z3_API Z3_rcf_interval(Z3_context c, Z3_rcf_num a, int * lower_is_inf, int * lower_is_open, Z3_rcf_num * lower, int * upper_is_inf, int * upper_is_open, Z3_rcf_num * upper) {
        Z3_TRY;
        LOG_Z3_rcf_interval(c, a, lower_is_inf, lower_is_open, lower, upper_is_inf, upper_is_open, upper);
        RESET_ERROR_CODE();
        reset_rcf_cancel(c);
        rcnumeral r_lower, r_upper;
        bool r = rcfm(c).get_interval(to_rcnumeral(a), *lower_is_inf, *lower_is_open, r_lower, *upper_is_inf, *upper_is_open, r_upper);
        *lower = from_rcnumeral(r_lower);
        *upper = from_rcnumeral(r_upper);
        return r;
        Z3_CATCH_RETURN(0);
    }

    unsigned Z3_API Z3_rcf_num_sign_conditions(Z3_context c, Z3_rcf_num a)
    {
        Z3_TRY;
        LOG_Z3_rcf_num_sign_conditions(c, a);
        RESET_ERROR_CODE();
        reset_rcf_cancel(c);
        return rcfm(c).num_sign_conditions(to_rcnumeral(a));
        Z3_CATCH_RETURN(0);
    }

    int Z3_API Z3_rcf_sign_condition_sign(Z3_context c, Z3_rcf_num a, unsigned i)
    {
        Z3_TRY;
        LOG_Z3_rcf_sign_condition_sign(c, a, i);
        RESET_ERROR_CODE();
        reset_rcf_cancel(c);
        return rcfm(c).get_sign_condition_sign(to_rcnumeral(a), i);
        Z3_CATCH_RETURN(0);
    }

    unsigned Z3_API Z3_rcf_num_sign_condition_coefficients(Z3_context c, Z3_rcf_num a, unsigned i)
    {
        Z3_TRY;
        LOG_Z3_rcf_num_sign_condition_coefficients(c, a, i);
        RESET_ERROR_CODE();
        reset_rcf_cancel(c);
        return rcfm(c).num_sign_condition_coefficients(to_rcnumeral(a), i);
        Z3_CATCH_RETURN(0);
    }

    Z3_rcf_num Z3_API Z3_rcf_sign_condition_coefficient(Z3_context c, Z3_rcf_num a, unsigned i, unsigned j)
    {
        Z3_TRY;
        LOG_Z3_rcf_sign_condition_coefficient(c, a, i, j);
        RESET_ERROR_CODE();
        reset_rcf_cancel(c);
        return from_rcnumeral(rcfm(c).get_sign_condition_coefficient(to_rcnumeral(a), i, j));
        Z3_CATCH_RETURN(nullptr);
    }
};
