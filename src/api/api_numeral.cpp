/*++
Copyright (c) 2012 Microsoft Corporation

Module Name:

    api_numeral.cpp

Abstract:
    API for handling numerals in Z3

Author:

    Leonardo de Moura (leonardo) 2012-02-29.

Revision History:

--*/
#include<iostream>
#include "api/z3.h"
#include "api/api_log_macros.h"
#include "api/api_context.h"
#include "api/api_util.h"
#include "ast/arith_decl_plugin.h"
#include "ast/bv_decl_plugin.h"
#include "math/polynomial/algebraic_numbers.h"
#include "ast/fpa_decl_plugin.h"

bool is_numeral_sort(Z3_context c, Z3_sort ty) {
    sort * _ty = to_sort(ty);
    family_id fid  = _ty->get_family_id();
    if (fid != mk_c(c)->get_arith_fid() &&
        fid != mk_c(c)->get_bv_fid() &&
        fid != mk_c(c)->get_datalog_fid() &&
        fid != mk_c(c)->get_fpa_fid()) {
        return false;
    }
    return true;
}

bool check_numeral_sort(Z3_context c, Z3_sort ty) {
    bool is_num = is_numeral_sort(c, ty);
    if (!is_num) {
        SET_ERROR_CODE(Z3_INVALID_ARG);
    }
    return is_num;
}

extern "C" {

    Z3_ast Z3_API Z3_mk_numeral(Z3_context c, const char* n, Z3_sort ty) {
        Z3_TRY;
        LOG_Z3_mk_numeral(c, n, ty);
        RESET_ERROR_CODE();
        if (!check_numeral_sort(c, ty)) {
            RETURN_Z3(nullptr);
        }
        if (!n) {
            SET_ERROR_CODE(Z3_INVALID_ARG);
            RETURN_Z3(nullptr);
        }
        sort * _ty = to_sort(ty);
        bool is_float = mk_c(c)->fpautil().is_float(_ty);
        std::string fixed_num;
        char const* m = n;
        while (*m) {
            if (!(('0' <= *m && *m <= '9') ||
                ('/' == *m) || ('-' == *m) ||
                (' ' == *m) || ('\n' == *m) ||
                ('.' == *m) || ('e' == *m) ||
                ('E' == *m) ||
                (is_float && 
                    (('p' == *m) ||
                     ('P' == *m) ||
                     ('+' == *m))))) {
                SET_ERROR_CODE(Z3_PARSER_ERROR);
                RETURN_Z3(nullptr);
            }
            ++m;
        }
        ast * a = nullptr;
        if (_ty->get_family_id() == mk_c(c)->get_fpa_fid()) {
            // avoid expanding floats into huge rationals.
            fpa_util & fu = mk_c(c)->fpautil();
            scoped_mpf t(fu.fm());
            fu.fm().set(t, fu.get_ebits(_ty), fu.get_sbits(_ty), MPF_ROUND_TOWARD_ZERO, n);
            a = fu.mk_value(t);
            mk_c(c)->save_ast_trail(a);
        }
        else
            a = mk_c(c)->mk_numeral_core(rational(n), _ty);
        RETURN_Z3(of_ast(a));
        Z3_CATCH_RETURN(nullptr);
    }

    Z3_ast Z3_API Z3_mk_int(Z3_context c, int value, Z3_sort ty) {
        Z3_TRY;
        LOG_Z3_mk_int(c, value, ty);
        RESET_ERROR_CODE();
        if (!check_numeral_sort(c, ty)) {
            RETURN_Z3(nullptr);
        }
        ast * a = mk_c(c)->mk_numeral_core(rational(value), to_sort(ty));
        RETURN_Z3(of_ast(a));
        Z3_CATCH_RETURN(nullptr);
    }

    Z3_ast Z3_API Z3_mk_unsigned_int(Z3_context c, unsigned value, Z3_sort ty) {
        Z3_TRY;
        LOG_Z3_mk_unsigned_int(c, value, ty);
        RESET_ERROR_CODE();
        if (!check_numeral_sort(c, ty)) {
            RETURN_Z3(nullptr);
        }
        ast * a = mk_c(c)->mk_numeral_core(rational(value), to_sort(ty));
        RETURN_Z3(of_ast(a));
        Z3_CATCH_RETURN(nullptr);
    }

    Z3_ast Z3_API Z3_mk_int64(Z3_context c, int64_t value, Z3_sort ty) {
        Z3_TRY;
        LOG_Z3_mk_int64(c, value, ty);
        RESET_ERROR_CODE();
        if (!check_numeral_sort(c, ty)) {
            RETURN_Z3(nullptr);
        }
        rational n(value, rational::i64());
        ast* a = mk_c(c)->mk_numeral_core(n, to_sort(ty));
        RETURN_Z3(of_ast(a));
        Z3_CATCH_RETURN(nullptr);
    }

    Z3_ast Z3_API Z3_mk_unsigned_int64(Z3_context c, uint64_t value, Z3_sort ty) {
        Z3_TRY;
        LOG_Z3_mk_unsigned_int64(c, value, ty);
        RESET_ERROR_CODE();
        if (!check_numeral_sort(c, ty)) {
            RETURN_Z3(nullptr);
        }
        rational n(value, rational::ui64());
        ast * a = mk_c(c)->mk_numeral_core(n, to_sort(ty));
        RETURN_Z3(of_ast(a));
        Z3_CATCH_RETURN(nullptr);
    }

    Z3_bool Z3_API Z3_is_numeral_ast(Z3_context c, Z3_ast a) {
        Z3_TRY;
        LOG_Z3_is_numeral_ast(c, a);
        RESET_ERROR_CODE();
        expr* e = to_expr(a);
        return
            mk_c(c)->autil().is_numeral(e) ||
            mk_c(c)->bvutil().is_numeral(e) ||
            mk_c(c)->fpautil().is_numeral(e) ||
            mk_c(c)->fpautil().is_rm_numeral(e) ||
            mk_c(c)->datalog_util().is_numeral_ext(e);
        Z3_CATCH_RETURN(Z3_FALSE);
    }

    Z3_bool Z3_API Z3_get_numeral_rational(Z3_context c, Z3_ast a, rational& r) {
        Z3_TRY;
        // This function is not part of the public API
        RESET_ERROR_CODE();
        expr* e = to_expr(a);
        if (!e) {
            SET_ERROR_CODE(Z3_INVALID_ARG);
            return Z3_FALSE;
        }
        if (mk_c(c)->autil().is_numeral(e, r)) {
            return Z3_TRUE;
        }
        unsigned bv_size;
        if (mk_c(c)->bvutil().is_numeral(e, r, bv_size)) {
            return Z3_TRUE;
        }
        uint64_t v;
        if (mk_c(c)->datalog_util().is_numeral(e, v)) {
            r = rational(v, rational::ui64());
            return Z3_TRUE;
        }
        return Z3_FALSE;
        Z3_CATCH_RETURN(Z3_FALSE);
    }


    Z3_string Z3_API Z3_get_numeral_string(Z3_context c, Z3_ast a) {
        Z3_TRY;
        // This function invokes Z3_get_numeral_rational, but it is still ok to add LOG command here because it does not return a Z3 object.
        LOG_Z3_get_numeral_string(c, a);
        RESET_ERROR_CODE();
        rational r;
        Z3_bool ok = Z3_get_numeral_rational(c, a, r);
        if (ok == Z3_TRUE) {
            return mk_c(c)->mk_external_string(r.to_string());
        }
        else {
            // floats are separated from all others to avoid huge rationals.
            fpa_util & fu = mk_c(c)->fpautil();
            scoped_mpf tmp(fu.fm());
            mpf_rounding_mode rm;
            if (mk_c(c)->fpautil().is_rm_numeral(to_expr(a), rm)) {
                switch (rm) {
                case OP_FPA_RM_NEAREST_TIES_TO_EVEN:
                    return mk_c(c)->mk_external_string("roundNearestTiesToEven");
                    break;
                case OP_FPA_RM_NEAREST_TIES_TO_AWAY:
                    return mk_c(c)->mk_external_string("roundNearestTiesToAway");
                    break;
                case OP_FPA_RM_TOWARD_POSITIVE:
                    return mk_c(c)->mk_external_string("roundTowardPositive");
                    break;
                case OP_FPA_RM_TOWARD_NEGATIVE:
                    return mk_c(c)->mk_external_string("roundTowardNegative");
                    break;
                case OP_FPA_RM_TOWARD_ZERO:
                default:
                    return mk_c(c)->mk_external_string("roundTowardZero");
                    break;
                }
            }
            else if (mk_c(c)->fpautil().is_numeral(to_expr(a), tmp)) {
                return mk_c(c)->mk_external_string(fu.fm().to_string(tmp));
            }
            else {
                SET_ERROR_CODE(Z3_INVALID_ARG);
                return "";
            }
        }
        Z3_CATCH_RETURN("");
    }

    Z3_string Z3_API Z3_get_numeral_decimal_string(Z3_context c, Z3_ast a, unsigned precision) {
        Z3_TRY;
        LOG_Z3_get_numeral_decimal_string(c, a, precision);
        RESET_ERROR_CODE();
        expr* e = to_expr(a);
        if (!e) {
            SET_ERROR_CODE(Z3_INVALID_ARG);
            return "";
        }
        rational r;
        arith_util & u = mk_c(c)->autil();
        if (u.is_numeral(e, r) && !r.is_int()) {
            std::ostringstream buffer;
            r.display_decimal(buffer, precision);
            return mk_c(c)->mk_external_string(buffer.str());
        }
        if (u.is_irrational_algebraic_numeral(e)) {
            algebraic_numbers::anum const & n = u.to_irrational_algebraic_numeral(e);
            algebraic_numbers::manager & am   = u.am();
            std::ostringstream buffer;
            am.display_decimal(buffer, n, precision);
            return mk_c(c)->mk_external_string(buffer.str());
        }
        Z3_bool ok = Z3_get_numeral_rational(c, a, r);
        if (ok == Z3_TRUE) {
            return mk_c(c)->mk_external_string(r.to_string());
        }
        else {
            SET_ERROR_CODE(Z3_INVALID_ARG);
            return "";
        }
        Z3_CATCH_RETURN("");
    }

    Z3_bool Z3_API Z3_get_numeral_small(Z3_context c, Z3_ast a, int64_t* num, int64_t* den) {
        Z3_TRY;
        // This function invokes Z3_get_numeral_rational, but it is still ok to add LOG command here because it does not return a Z3 object.
        LOG_Z3_get_numeral_small(c, a, num, den);
        RESET_ERROR_CODE();
        rational r;
        Z3_bool ok = Z3_get_numeral_rational(c, a, r);
        if (ok == Z3_TRUE) {
            rational n = numerator(r);
            rational d = denominator(r);
            if (n.is_int64() && d.is_int64()) {
                *num = n.get_int64();
                *den = d.get_int64();
                return Z3_TRUE;
            }
            else {
                return Z3_FALSE;
            }
        }
        SET_ERROR_CODE(Z3_INVALID_ARG);
        return Z3_FALSE;
        Z3_CATCH_RETURN(Z3_FALSE);
    }


    Z3_bool Z3_API Z3_get_numeral_int(Z3_context c, Z3_ast v, int* i) {
        Z3_TRY;
        // This function invokes Z3_get_numeral_int64, but it is still ok to add LOG command here because it does not return a Z3 object.
        LOG_Z3_get_numeral_int(c, v, i);
        RESET_ERROR_CODE();
        if (!i) {
            SET_ERROR_CODE(Z3_INVALID_ARG);
            return Z3_FALSE;
        }
        int64_t l;
        if (Z3_get_numeral_int64(c, v, &l) && l >= INT_MIN && l <= INT_MAX) {
            *i = static_cast<int>(l);
            return Z3_TRUE;
        }
        return Z3_FALSE;
        Z3_CATCH_RETURN(Z3_FALSE);
    }

    Z3_bool Z3_API Z3_get_numeral_uint(Z3_context c, Z3_ast v, unsigned* u) {
        Z3_TRY;
        // This function invokes Z3_get_numeral_uint64, but it is still ok to add LOG command here because it does not return a Z3 object.
        LOG_Z3_get_numeral_uint(c, v, u);
        RESET_ERROR_CODE();
        if (!u) {
            SET_ERROR_CODE(Z3_INVALID_ARG);
            return Z3_FALSE;
        }
        uint64_t l;
        if (Z3_get_numeral_uint64(c, v, &l) && (l <= 0xFFFFFFFF)) {
            *u = static_cast<unsigned>(l);
            return Z3_TRUE;
        }
        return Z3_FALSE;
        Z3_CATCH_RETURN(Z3_FALSE);
    }

    Z3_bool Z3_API Z3_get_numeral_uint64(Z3_context c, Z3_ast v, uint64_t* u) {
        Z3_TRY;
        // This function invokes Z3_get_numeral_rational, but it is still ok to add LOG command here because it does not return a Z3 object.
        LOG_Z3_get_numeral_uint64(c, v, u);
        RESET_ERROR_CODE();
        if (!u) {
            SET_ERROR_CODE(Z3_INVALID_ARG);
            return Z3_FALSE;
        }
        rational r;
        Z3_bool ok = Z3_get_numeral_rational(c, v, r);
        SASSERT(u);
        if (ok == Z3_TRUE && r.is_uint64()) {
            *u = r.get_uint64();
            return ok;
        }
        return Z3_FALSE;
        Z3_CATCH_RETURN(Z3_FALSE);
    }

    Z3_bool Z3_API Z3_get_numeral_int64(Z3_context c, Z3_ast v, int64_t* i) {
        Z3_TRY;
        // This function invokes Z3_get_numeral_rational, but it is still ok to add LOG command here because it does not return a Z3 object.
        LOG_Z3_get_numeral_int64(c, v, i);
        RESET_ERROR_CODE();
        if (!i) {
            SET_ERROR_CODE(Z3_INVALID_ARG);
            return Z3_FALSE;
        }
        rational r;
        Z3_bool ok = Z3_get_numeral_rational(c, v, r);
        if (ok == Z3_TRUE && r.is_int64()) {
            *i = r.get_int64();
            return ok;
        }
        return Z3_FALSE;
        Z3_CATCH_RETURN(Z3_FALSE);
    }

    Z3_bool Z3_API Z3_get_numeral_rational_int64(Z3_context c, Z3_ast v, int64_t* num, int64_t* den) {
        Z3_TRY;
        // This function invokes Z3_get_numeral_rational, but it is still ok to add LOG command here because it does not return a Z3 object.
        LOG_Z3_get_numeral_rational_int64(c, v, num, den);
        RESET_ERROR_CODE();
        if (!num || !den) {
            SET_ERROR_CODE(Z3_INVALID_ARG);
            return Z3_FALSE;
        }
        rational r;
        Z3_bool ok = Z3_get_numeral_rational(c, v, r);
        if (ok != Z3_TRUE) {
            return ok;
        }
        rational n = numerator(r);
        rational d = denominator(r);
        if (n.is_int64() && d.is_int64()) {
            *num = n.get_int64();
            *den = d.get_int64();
            return ok;
        }
        return Z3_FALSE;
        Z3_CATCH_RETURN(Z3_FALSE);
    }

    Z3_ast Z3_API Z3_mk_bv_numeral(Z3_context c, unsigned sz, Z3_bool const* bits) {
        Z3_TRY;
        LOG_Z3_mk_bv_numeral(c, sz, bits);
        RESET_ERROR_CODE();
        rational r(0);
        for (unsigned i = 0; i < sz; ++i) {
            if (bits[i]) r += rational::power_of_two(i);
        }
        ast * a = mk_c(c)->mk_numeral_core(r, mk_c(c)->bvutil().mk_sort(sz));
        RETURN_Z3(of_ast(a));
        Z3_CATCH_RETURN(nullptr);
    }

};
