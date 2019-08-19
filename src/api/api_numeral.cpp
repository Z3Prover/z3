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
#include<cmath>
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
    if (!ty) return false;
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

static bool check_numeral_sort(Z3_context c, Z3_sort ty) {
    bool is_num = is_numeral_sort(c, ty);
    if (!is_num) {
        SET_ERROR_CODE(Z3_INVALID_ARG, nullptr);
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
            SET_ERROR_CODE(Z3_INVALID_ARG, nullptr);
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
                ('E' == *m) || ('+' == *m) ||
                (is_float &&
                    (('p' == *m) ||
                     ('P' == *m))))) {
                SET_ERROR_CODE(Z3_PARSER_ERROR, nullptr);
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

    bool Z3_API Z3_is_numeral_ast(Z3_context c, Z3_ast a) {
        Z3_TRY;
        LOG_Z3_is_numeral_ast(c, a);
        RESET_ERROR_CODE();
        CHECK_IS_EXPR(a, false);
        expr* e = to_expr(a);
        return
            mk_c(c)->autil().is_numeral(e) ||
            mk_c(c)->bvutil().is_numeral(e) ||
            mk_c(c)->fpautil().is_numeral(e) ||
            mk_c(c)->fpautil().is_rm_numeral(e) ||
            mk_c(c)->datalog_util().is_numeral_ext(e);
        Z3_CATCH_RETURN(false);
    }

    bool Z3_API Z3_get_numeral_rational(Z3_context c, Z3_ast a, rational& r) {
        Z3_TRY;
        // This function is not part of the public API
        RESET_ERROR_CODE();
        CHECK_IS_EXPR(a, false);
        expr* e = to_expr(a);
        if (mk_c(c)->autil().is_numeral(e, r)) {
            return true;
        }
        unsigned bv_size;
        if (mk_c(c)->bvutil().is_numeral(e, r, bv_size)) {
            return true;
        }
        uint64_t v;
        if (mk_c(c)->datalog_util().is_numeral(e, v)) {
            r = rational(v, rational::ui64());
            return true;
        }
        return false;
        Z3_CATCH_RETURN(false);
    }


    Z3_string Z3_API Z3_get_numeral_string(Z3_context c, Z3_ast a) {
        Z3_TRY;
        // This function invokes Z3_get_numeral_rational, but it is still ok to add LOG command here because it does not return a Z3 object.
        LOG_Z3_get_numeral_string(c, a);
        RESET_ERROR_CODE();
        CHECK_IS_EXPR(a, "");
        rational r;
        bool ok = Z3_get_numeral_rational(c, a, r);
        if (ok) {
            return mk_c(c)->mk_external_string(r.to_string());
        }
        else {
            fpa_util & fu = mk_c(c)->fpautil();
            scoped_mpf tmp(fu.fm());
            mpf_rounding_mode rm;
            if (mk_c(c)->fpautil().is_rm_numeral(to_expr(a), rm)) {
                switch (rm) {
                case MPF_ROUND_NEAREST_TEVEN:
                    return mk_c(c)->mk_external_string("roundNearestTiesToEven");
                    break;
                case MPF_ROUND_NEAREST_TAWAY:
                    return mk_c(c)->mk_external_string("roundNearestTiesToAway");
                    break;
                case MPF_ROUND_TOWARD_POSITIVE:
                    return mk_c(c)->mk_external_string("roundTowardPositive");
                    break;
                case MPF_ROUND_TOWARD_NEGATIVE:
                    return mk_c(c)->mk_external_string("roundTowardNegative");
                    break;
                case MPF_ROUND_TOWARD_ZERO:
                default:
                    return mk_c(c)->mk_external_string("roundTowardZero");
                    break;
                }
            }
            else if (mk_c(c)->fpautil().is_numeral(to_expr(a), tmp)) {
                std::ostringstream buffer;
                fu.fm().display_smt2(buffer, tmp, false);
                return mk_c(c)->mk_external_string(buffer.str());
            }
            else {
                SET_ERROR_CODE(Z3_INVALID_ARG, nullptr);
                return "";
            }
        }
        Z3_CATCH_RETURN("");
    }

    double Z3_API Z3_get_numeral_double(Z3_context c, Z3_ast a) {
        LOG_Z3_get_numeral_double(c, a);
        RESET_ERROR_CODE();
        if (!is_expr(a)) {
            SET_ERROR_CODE(Z3_INVALID_ARG, nullptr);
            return NAN;
        }
        expr* e = to_expr(a);
        fpa_util & fu = mk_c(c)->fpautil();
        scoped_mpf tmp(fu.fm());
        if (!mk_c(c)->fpautil().is_numeral(e, tmp) ||
            tmp.get().get_ebits() > 11 ||
            tmp.get().get_sbits() > 53) {
            SET_ERROR_CODE(Z3_INVALID_ARG, nullptr);
            return NAN;
        }
        return fu.fm().to_double(tmp);
    }

    Z3_string Z3_API Z3_get_numeral_decimal_string(Z3_context c, Z3_ast a, unsigned precision) {
        Z3_TRY;
        LOG_Z3_get_numeral_decimal_string(c, a, precision);
        RESET_ERROR_CODE();
        CHECK_IS_EXPR(a, "");
        expr* e = to_expr(a);
        rational r;
        arith_util & u = mk_c(c)->autil();
        fpa_util & fu = mk_c(c)->fpautil();
        scoped_mpf ftmp(fu.fm());
        mpf_rounding_mode rm;
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
        else if (mk_c(c)->fpautil().is_rm_numeral(to_expr(a), rm))
            return Z3_get_numeral_string(c, a);
        else if (mk_c(c)->fpautil().is_numeral(to_expr(a), ftmp)) {
            std::ostringstream buffer;
            fu.fm().display_decimal(buffer, ftmp, 12);
            return mk_c(c)->mk_external_string(buffer.str());
        }
        else if (Z3_get_numeral_rational(c, a, r)) {
            return mk_c(c)->mk_external_string(r.to_string());
        }
        else {
            SET_ERROR_CODE(Z3_INVALID_ARG, nullptr);
            return "";
        }
        Z3_CATCH_RETURN("");
    }

    bool Z3_API Z3_get_numeral_small(Z3_context c, Z3_ast a, int64_t* num, int64_t* den) {
        Z3_TRY;
        // This function invokes Z3_get_numeral_rational, but it is still ok to add LOG command here because it does not return a Z3 object.
        LOG_Z3_get_numeral_small(c, a, num, den);
        RESET_ERROR_CODE();
        CHECK_IS_EXPR(a, false);
        rational r;
        bool ok = Z3_get_numeral_rational(c, a, r);
        if (ok) {
            rational n = numerator(r);
            rational d = denominator(r);
            if (n.is_int64() && d.is_int64()) {
                *num = n.get_int64();
                *den = d.get_int64();
                return true;
            }
            else {
                return false;
            }
        }
        SET_ERROR_CODE(Z3_INVALID_ARG, nullptr);
        return false;
        Z3_CATCH_RETURN(false);
    }


    bool Z3_API Z3_get_numeral_int(Z3_context c, Z3_ast v, int* i) {
        Z3_TRY;
        // This function invokes Z3_get_numeral_int64, but it is still ok to add LOG command here because it does not return a Z3 object.
        LOG_Z3_get_numeral_int(c, v, i);
        RESET_ERROR_CODE();
        CHECK_IS_EXPR(v, false);
        if (!i) {
            SET_ERROR_CODE(Z3_INVALID_ARG, nullptr);
            return false;
        }
        int64_t l;
        if (Z3_get_numeral_int64(c, v, &l) && l >= INT_MIN && l <= INT_MAX) {
            *i = static_cast<int>(l);
            return true;
        }
        return false;
        Z3_CATCH_RETURN(false);
    }

    bool Z3_API Z3_get_numeral_uint(Z3_context c, Z3_ast v, unsigned* u) {
        Z3_TRY;
        // This function invokes Z3_get_numeral_uint64, but it is still ok to add LOG command here because it does not return a Z3 object.
        LOG_Z3_get_numeral_uint(c, v, u);
        RESET_ERROR_CODE();
        CHECK_IS_EXPR(v, false);
        if (!u) {
            SET_ERROR_CODE(Z3_INVALID_ARG, nullptr);
            return false;
        }
        uint64_t l;
        if (Z3_get_numeral_uint64(c, v, &l) && (l <= 0xFFFFFFFF)) {
            *u = static_cast<unsigned>(l);
            return true;
        }
        return false;
        Z3_CATCH_RETURN(false);
    }

    bool Z3_API Z3_get_numeral_uint64(Z3_context c, Z3_ast v, uint64_t* u) {
        Z3_TRY;
        // This function invokes Z3_get_numeral_rational, but it is still ok to add LOG command here because it does not return a Z3 object.
        LOG_Z3_get_numeral_uint64(c, v, u);
        RESET_ERROR_CODE();
        CHECK_IS_EXPR(v, false);
        if (!u) {
            SET_ERROR_CODE(Z3_INVALID_ARG, nullptr);
            return false;
        }
        rational r;
        bool ok = Z3_get_numeral_rational(c, v, r);
        SASSERT(u);
        if (ok && r.is_uint64()) {
            *u = r.get_uint64();
            return ok;
        }
        return false;
        Z3_CATCH_RETURN(false);
    }

    bool Z3_API Z3_get_numeral_int64(Z3_context c, Z3_ast v, int64_t* i) {
        Z3_TRY;
        // This function invokes Z3_get_numeral_rational, but it is still ok to add LOG command here because it does not return a Z3 object.
        LOG_Z3_get_numeral_int64(c, v, i);
        RESET_ERROR_CODE();
        CHECK_IS_EXPR(v, false);
        if (!i) {
            SET_ERROR_CODE(Z3_INVALID_ARG, nullptr);
            return false;
        }
        rational r;
        bool ok = Z3_get_numeral_rational(c, v, r);
        if (ok && r.is_int64()) {
            *i = r.get_int64();
            return ok;
        }
        return false;
        Z3_CATCH_RETURN(false);
    }

    bool Z3_API Z3_get_numeral_rational_int64(Z3_context c, Z3_ast v, int64_t* num, int64_t* den) {
        Z3_TRY;
        // This function invokes Z3_get_numeral_rational, but it is still ok to add LOG command here because it does not return a Z3 object.
        LOG_Z3_get_numeral_rational_int64(c, v, num, den);
        RESET_ERROR_CODE();
        CHECK_IS_EXPR(v, false);
        if (!num || !den) {
            SET_ERROR_CODE(Z3_INVALID_ARG, nullptr);
            return false;
        }
        rational r;
        bool ok = Z3_get_numeral_rational(c, v, r);
        if (ok != true) {
            return ok;
        }
        rational n = numerator(r);
        rational d = denominator(r);
        if (n.is_int64() && d.is_int64()) {
            *num = n.get_int64();
            *den = d.get_int64();
            return ok;
        }
        return false;
        Z3_CATCH_RETURN(false);
    }

    Z3_ast Z3_API Z3_mk_bv_numeral(Z3_context c, unsigned sz, bool const* bits) {
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
