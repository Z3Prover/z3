/*++
Copyright (c) 2012 Microsoft Corporation

Module Name:

    float_rewriter.h

Abstract:

    Basic rewriting rules for floating point numbers.

Author:

    Leonardo (leonardo) 2012-02-02

Notes:

--*/
#pragma once

#include "ast/ast.h"
#include "ast/rewriter/rewriter.h"
#include "ast/fpa_decl_plugin.h"
#include "ast/expr_map.h"
#include "util/params.h"
#include "util/mpf.h"

class fpa_rewriter {
    fpa_util      m_util;
    mpf_manager & m_fm;
    bool          m_hi_fp_unspecified;

    app * mk_eq_nan(expr * arg);
    app * mk_neq_nan(expr * arg);

    br_status mk_to_bv(func_decl * f, expr * arg1, expr * arg2, bool is_signed, expr_ref & result);
    br_status mk_to_bv_unspecified(func_decl * f, expr_ref & result);

public:
    fpa_rewriter(ast_manager & m, params_ref const & p = params_ref());

    ast_manager & m() const { return m_util.m(); }
    family_id get_fid() const { return m_util.get_fid(); }

    void updt_params(params_ref const & p);
    static void get_param_descrs(param_descrs & r);

    br_status mk_app_core(func_decl * f, unsigned num_args, expr * const * args, expr_ref & result);
    br_status mk_eq_core(expr * arg1, expr * arg2, expr_ref & result);

    br_status mk_add(expr * arg1, expr * arg2, expr * arg3, expr_ref & result);
    br_status mk_sub(expr * arg1, expr * arg2, expr * arg3, expr_ref & result);
    br_status mk_mul(expr * arg1, expr * arg2, expr * arg3, expr_ref & result);
    br_status mk_div(expr * arg1, expr * arg2, expr * arg3, expr_ref & result);
    br_status mk_neg(expr * arg1, expr_ref & result);
    br_status mk_rem(expr * arg1, expr * arg2, expr_ref & result);
    br_status mk_abs(expr * arg1, expr_ref & result);
    br_status mk_min(expr * arg1, expr * arg2, expr_ref & result);
    br_status mk_max(expr * arg1, expr * arg2, expr_ref & result);
    br_status mk_fma(expr * arg1, expr * arg2, expr * arg3, expr * arg4, expr_ref & result);
    br_status mk_sqrt(expr * arg1, expr * arg2, expr_ref & result);
    br_status mk_round_to_integral(expr * arg1, expr * arg2, expr_ref & result);
    br_status mk_float_eq(expr * arg1, expr * arg2, expr_ref & result);
    br_status mk_lt(expr * arg1, expr * arg2, expr_ref & result);
    br_status mk_gt(expr * arg1, expr * arg2, expr_ref & result);
    br_status mk_le(expr * arg1, expr * arg2, expr_ref & result);
    br_status mk_ge(expr * arg1, expr * arg2, expr_ref & result);
    br_status mk_is_zero(expr * arg1, expr_ref & result);
    br_status mk_is_nzero(expr * arg1, expr_ref & result);
    br_status mk_is_pzero(expr * arg1, expr_ref & result);
    br_status mk_is_nan(expr * arg1, expr_ref & result);
    br_status mk_is_inf(expr * arg1, expr_ref & result);
    br_status mk_is_normal(expr * arg1, expr_ref & result);
    br_status mk_is_subnormal(expr * arg1, expr_ref & result);
    br_status mk_is_negative(expr * arg1, expr_ref & result);
    br_status mk_is_positive(expr * arg1, expr_ref & result);

    br_status mk_to_fp(func_decl * f, unsigned num_args, expr * const * args, expr_ref & result);
    br_status mk_to_fp_unsigned(func_decl * f, expr * arg1, expr * arg2, expr_ref & result);

    br_status mk_bv2rm(expr * arg, expr_ref & result);
    br_status mk_fp(expr * sgn, expr * exp, expr * sig, expr_ref & result);
    br_status mk_to_ubv(func_decl * f, expr * arg1, expr * arg2, expr_ref & result);
    br_status mk_to_sbv(func_decl * f, expr * arg1, expr * arg2, expr_ref & result);
    br_status mk_to_ieee_bv(func_decl * f, expr * arg, expr_ref & result);
    br_status mk_to_real(expr * arg, expr_ref & result);
    br_status mk_min_i(func_decl * f, expr * arg1, expr * arg2, expr_ref & result);
    br_status mk_max_i(func_decl * f, expr * arg1, expr * arg2, expr_ref & result);

    br_status mk_bvwrap(expr * arg, expr_ref & result);
};

