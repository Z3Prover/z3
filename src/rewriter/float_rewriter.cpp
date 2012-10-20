/*++
Copyright (c) 2012 Microsoft Corporation

Module Name:

    float_rewriter.cpp

Abstract:

    Basic rewriting rules for floating point numbers.

Author:

    Leonardo (leonardo) 2012-02-02

Notes:

--*/
#include"float_rewriter.h"

float_rewriter::float_rewriter(ast_manager & m, params_ref const & p):
    m_util(m) {
    updt_params(p);
}

float_rewriter::~float_rewriter() {
}

void float_rewriter::updt_params(params_ref const & p) {
}
 
void float_rewriter::get_param_descrs(param_descrs & r) {
}

br_status float_rewriter::mk_app_core(func_decl * f, unsigned num_args, expr * const * args, expr_ref & result) {
    br_status st = BR_FAILED;
    SASSERT(f->get_family_id() == get_fid());
    switch (f->get_decl_kind()) {
    case OP_TO_FLOAT:        st = mk_to_float(f, num_args, args, result); break;
    case OP_FLOAT_ADD:       SASSERT(num_args == 3); st = mk_add(args[0], args[1], args[2], result); break;
    case OP_FLOAT_SUB:       SASSERT(num_args == 3); st = mk_sub(args[0], args[1], args[2], result); break;
    case OP_FLOAT_UMINUS:    SASSERT(num_args == 1); st = mk_uminus(args[0], result); break;
    case OP_FLOAT_MUL:       SASSERT(num_args == 3); st = mk_mul(args[0], args[1], args[2], result); break;
    case OP_FLOAT_DIV:       SASSERT(num_args == 3); st = mk_div(args[0], args[1], args[2], result); break;
    case OP_FLOAT_REM:       SASSERT(num_args == 2); st = mk_rem(args[0], args[1], result); break;
    case OP_FLOAT_ABS:       SASSERT(num_args == 1); st = mk_abs(args[0], result); break;
    case OP_FLOAT_MIN:       SASSERT(num_args == 2); st = mk_min(args[0], args[1], result); break;
    case OP_FLOAT_MAX:       SASSERT(num_args == 2); st = mk_max(args[0], args[1], result); break;
    case OP_FLOAT_FUSED_MA:  SASSERT(num_args == 4); st = mk_fused_ma(args[0], args[1], args[2], args[3], result); break;
    case OP_FLOAT_SQRT:      SASSERT(num_args == 2); st = mk_sqrt(args[0], args[1], result); break;
    case OP_FLOAT_ROUND_TO_INTEGRAL: SASSERT(num_args == 2); st = mk_round(args[0], args[1], result); break;

    case OP_FLOAT_EQ:        SASSERT(num_args == 2); st = mk_float_eq(args[0], args[1], result); break; 
    case OP_FLOAT_LT:        SASSERT(num_args == 2); st = mk_lt(args[0], args[1], result); break;
    case OP_FLOAT_GT:        SASSERT(num_args == 2); st = mk_gt(args[0], args[1], result); break;
    case OP_FLOAT_LE:        SASSERT(num_args == 2); st = mk_le(args[0], args[1], result); break;
    case OP_FLOAT_GE:        SASSERT(num_args == 2); st = mk_ge(args[0], args[1], result); break;
    case OP_FLOAT_IS_ZERO:   SASSERT(num_args == 1); st = mk_is_zero(args[0], result); break;
    case OP_FLOAT_IS_NZERO:  SASSERT(num_args == 1); st = mk_is_nzero(args[0], result); break;
    case OP_FLOAT_IS_PZERO:  SASSERT(num_args == 1); st = mk_is_pzero(args[0], result); break;
    case OP_FLOAT_IS_SIGN_MINUS: SASSERT(num_args == 1); st = mk_is_sign_minus(args[0], result); break;
    }
    return st;
}

br_status float_rewriter::mk_to_float(func_decl * f, unsigned num_args, expr * const * args, expr_ref & result) {
    SASSERT(f->get_num_parameters() == 2);
    SASSERT(f->get_parameter(0).is_int());
    SASSERT(f->get_parameter(1).is_int());
    unsigned ebits = f->get_parameter(0).get_int();
    unsigned sbits = f->get_parameter(1).get_int();

    if (num_args == 2) {
        mpf_rounding_mode rm;
        if (!m_util.is_rm(args[0], rm))
            return BR_FAILED;
        
        rational q;
        if (!m_util.au().is_numeral(args[1], q))
            return BR_FAILED;
        
        mpf v;
        m_util.fm().set(v, ebits, sbits, rm, q.to_mpq());
        result = m_util.mk_value(v);
        m_util.fm().del(v);
        return BR_DONE;
    }
    else if (num_args == 3 && 
             m_util.is_rm(m().get_sort(args[0])) && 
             m_util.au().is_real(args[1]) &&
             m_util.au().is_int(args[2])) {

        mpf_rounding_mode rm;
        if (!m_util.is_rm(args[0], rm))
            return BR_FAILED;

        rational q;
        if (!m_util.au().is_numeral(args[1], q))
            return BR_FAILED;

        rational e;
        if (!m_util.au().is_numeral(args[2], e))
            return BR_FAILED;

        TRACE("fp_rewriter", tout << "q: " << q << ", e: " << e << "\n";);

        mpf v;
	    m_util.fm().set(v, ebits, sbits, rm, q.to_mpq(), e.to_mpq().numerator());
        result = m_util.mk_value(v);
        m_util.fm().del(v);
        return BR_DONE;
    }
    else {
        return BR_FAILED;
    }
}

br_status float_rewriter::mk_add(expr * arg1, expr * arg2, expr * arg3, expr_ref & result) {    
    mpf_rounding_mode rm;
    if (m_util.is_rm(arg1, rm)) {
        scoped_mpf v2(m_util.fm()), v3(m_util.fm());
        if (m_util.is_value(arg2, v2) && m_util.is_value(arg3, v3)) {
            scoped_mpf t(m_util.fm());
            m_util.fm().add(rm, v2, v3, t);
            result = m_util.mk_value(t);
            return BR_DONE;
        }
    }

    return BR_FAILED;
}

br_status float_rewriter::mk_sub(expr * arg1, expr * arg2, expr * arg3, expr_ref & result) {
    // a - b = a + (-b)
    result = m_util.mk_add(arg1, arg2, m_util.mk_uminus(arg3));
    return BR_REWRITE2;
}

br_status float_rewriter::mk_mul(expr * arg1, expr * arg2, expr * arg3, expr_ref & result) {    
    mpf_rounding_mode rm;
    if (m_util.is_rm(arg1, rm)) {
        scoped_mpf v2(m_util.fm()), v3(m_util.fm());
        if (m_util.is_value(arg2, v2) && m_util.is_value(arg3, v3)) {
            scoped_mpf t(m_util.fm());
            m_util.fm().mul(rm, v2, v3, t);
            result = m_util.mk_value(t);
            return BR_DONE;
        }
    }

    return BR_FAILED;
}

br_status float_rewriter::mk_div(expr * arg1, expr * arg2, expr * arg3, expr_ref & result) {
    mpf_rounding_mode rm;
    if (m_util.is_rm(arg1, rm)) {
        scoped_mpf v2(m_util.fm()), v3(m_util.fm());
        if (m_util.is_value(arg2, v2) && m_util.is_value(arg3, v3)) {
            scoped_mpf t(m_util.fm());
            m_util.fm().div(rm, v2, v3, t);
            result = m_util.mk_value(t);
            return BR_DONE;
        }
    }

    return BR_FAILED;
}

br_status float_rewriter::mk_uminus(expr * arg1, expr_ref & result) {
    if (m_util.is_nan(arg1)) {
        // -nan --> nan
        result = arg1;
        return BR_DONE;
    }
    if (m_util.is_plus_inf(arg1)) {
        // - +oo --> -oo
        result = m_util.mk_minus_inf(m().get_sort(arg1));
        return BR_DONE;
    }
    if (m_util.is_minus_inf(arg1)) {
        // - -oo -> +oo
        result = m_util.mk_plus_inf(m().get_sort(arg1));
        return BR_DONE;
    }
    if (m_util.is_uminus(arg1)) {
        // - - a --> a
        result = to_app(arg1)->get_arg(0);
        return BR_DONE;
    }
    
    scoped_mpf v1(m_util.fm());
    if (m_util.is_value(arg1, v1)) {
        m_util.fm().neg(v1);
        result = m_util.mk_value(v1);
        return BR_DONE;
    }

    // TODO: more simplifications
    return BR_FAILED;
}

br_status float_rewriter::mk_rem(expr * arg1, expr * arg2, expr_ref & result) {
    scoped_mpf v1(m_util.fm()), v2(m_util.fm());
    if (m_util.is_value(arg1, v1) && m_util.is_value(arg2, v2)) {
        scoped_mpf t(m_util.fm());
        m_util.fm().rem(v1, v2, t);
        result = m_util.mk_value(t);
        return BR_DONE;
    }

    return BR_FAILED;
}

br_status float_rewriter::mk_abs(expr * arg1, expr_ref & result) {
    if (m_util.is_nan(arg1)) {
        result = arg1;
        return BR_DONE;
    }
    sort * s = m().get_sort(arg1);
    result = m().mk_ite(m_util.mk_lt(arg1, m_util.mk_pzero(s)),
                        m_util.mk_uminus(arg1),
                        arg1);
    return BR_REWRITE2;
}

br_status float_rewriter::mk_min(expr * arg1, expr * arg2, expr_ref & result) {
    if (m_util.is_nan(arg1)) {
        result = arg2;
        return BR_DONE;
    }
    if (m_util.is_nan(arg2)) {
        result = arg1;
        return BR_DONE;
    }
    // expand as using ite's
    result = m().mk_ite(mk_eq_nan(arg1),
                        arg2,
                        m().mk_ite(mk_eq_nan(arg2), 
                                   arg1,
                                   m().mk_ite(m_util.mk_lt(arg1, arg2),
                                              arg1,
                                              arg2)));
    return BR_REWRITE_FULL;
}

br_status float_rewriter::mk_max(expr * arg1, expr * arg2, expr_ref & result) {
    if (m_util.is_nan(arg1)) {
        result = arg2;
        return BR_DONE;
    }
    if (m_util.is_nan(arg2)) {
        result = arg1;
        return BR_DONE;
    }
    // expand as using ite's
    result = m().mk_ite(mk_eq_nan(arg1), 
                        arg2,
                        m().mk_ite(mk_eq_nan(arg2), 
                                   arg1,
                                   m().mk_ite(m_util.mk_gt(arg1, arg2),
                                              arg1,
                                              arg2)));
    return BR_REWRITE_FULL;
}

br_status float_rewriter::mk_fused_ma(expr * arg1, expr * arg2, expr * arg3, expr * arg4, expr_ref & result) {
    mpf_rounding_mode rm;
    if (m_util.is_rm(arg1, rm)) {
        scoped_mpf v2(m_util.fm()), v3(m_util.fm()), v4(m_util.fm());
        if (m_util.is_value(arg2, v2) && m_util.is_value(arg3, v3) && m_util.is_value(arg4, v4)) {
            scoped_mpf t(m_util.fm());
            m_util.fm().fused_mul_add(rm, v2, v3, v4, t);
            result = m_util.mk_value(t);
            return BR_DONE;
        }
    }

    return BR_FAILED;
}

br_status float_rewriter::mk_sqrt(expr * arg1, expr * arg2, expr_ref & result) {
    mpf_rounding_mode rm;
    if (m_util.is_rm(arg1, rm)) {
        scoped_mpf v2(m_util.fm());
        if (m_util.is_value(arg2, v2)) {
            scoped_mpf t(m_util.fm());
            m_util.fm().sqrt(rm, v2, t);
            result = m_util.mk_value(t);
            return BR_DONE;
        }
    }

    return BR_FAILED;
}

br_status float_rewriter::mk_round(expr * arg1, expr * arg2, expr_ref & result) {
    mpf_rounding_mode rm;
    if (m_util.is_rm(arg1, rm)) {
        scoped_mpf v2(m_util.fm());
        if (m_util.is_value(arg2, v2)) {
            scoped_mpf t(m_util.fm());
            m_util.fm().round_to_integral(rm, v2, t);
            result = m_util.mk_value(t);
            return BR_DONE;
        }
    }

    return BR_FAILED;
}

// This the floating point theory ==
br_status float_rewriter::mk_float_eq(expr * arg1, expr * arg2, expr_ref & result) {
    scoped_mpf v1(m_util.fm()), v2(m_util.fm());
    if (m_util.is_value(arg1, v1) && m_util.is_value(arg2, v2)) {
        result = (m_util.fm().eq(v1, v2)) ? m().mk_true() : m().mk_false();
        return BR_DONE;
    }

    return BR_FAILED;
}

// Return (= arg NaN)
app * float_rewriter::mk_eq_nan(expr * arg) {
    return m().mk_eq(arg, m_util.mk_nan(m().get_sort(arg)));
}

// Return (not (= arg NaN))
app * float_rewriter::mk_neq_nan(expr * arg) {
    return m().mk_not(mk_eq_nan(arg));
}

br_status float_rewriter::mk_lt(expr * arg1, expr * arg2, expr_ref & result) {
    if (m_util.is_nan(arg1) || m_util.is_nan(arg2)) {
        result = m().mk_false();
        return BR_DONE;
    }
    if (m_util.is_minus_inf(arg1)) {
        // -oo < arg2 -->  not(arg2 = -oo) and not(arg2 = NaN)
        result = m().mk_and(m().mk_not(m().mk_eq(arg2, arg1)), mk_neq_nan(arg2));
        return BR_REWRITE2;
    }
    if (m_util.is_minus_inf(arg2)) {
        // arg1 < -oo  --> false
        result = m().mk_false();
        return BR_DONE;
    }
    if (m_util.is_plus_inf(arg1)) {
        // +oo < arg2 --> false
        result = m().mk_false();
        return BR_DONE;
    }
    if (m_util.is_plus_inf(arg2)) {
        // arg1 < +oo --> not(arg1 = +oo) and not(arg1 = NaN)
        result = m().mk_and(m().mk_not(m().mk_eq(arg1, arg2)), mk_neq_nan(arg1));
        return BR_REWRITE2;
    }

    scoped_mpf v1(m_util.fm()), v2(m_util.fm());
    if (m_util.is_value(arg1, v1) && m_util.is_value(arg2, v2)) {
        result = (m_util.fm().lt(v1, v2)) ? m().mk_true() : m().mk_false();
        return BR_DONE;
    }

    // TODO: more simplifications
    return BR_FAILED;
}

br_status float_rewriter::mk_gt(expr * arg1, expr * arg2, expr_ref & result) {
    result = m_util.mk_lt(arg2, arg1);
    return BR_REWRITE1;
}

br_status float_rewriter::mk_le(expr * arg1, expr * arg2, expr_ref & result) {
    if (m_util.is_nan(arg1) || m_util.is_nan(arg2)) {
        result = m().mk_false();
        return BR_DONE;
    }
    scoped_mpf v1(m_util.fm()), v2(m_util.fm());
    if (m_util.is_value(arg1, v1) && m_util.is_value(arg2, v2)) {
        result = (m_util.fm().le(v1, v2)) ? m().mk_true() : m().mk_false();
        return BR_DONE;
    }

    return BR_FAILED;
}

br_status float_rewriter::mk_ge(expr * arg1, expr * arg2, expr_ref & result) {
    result = m_util.mk_le(arg2, arg1);
    return BR_REWRITE1;
}

br_status float_rewriter::mk_is_zero(expr * arg1, expr_ref & result) {
    scoped_mpf v(m_util.fm());
    if (m_util.is_value(arg1, v)) {
        result = (m_util.fm().is_zero(v)) ? m().mk_true() : m().mk_false();
        return BR_DONE;
    }

    return BR_FAILED;
}

br_status float_rewriter::mk_is_nzero(expr * arg1, expr_ref & result) {
    scoped_mpf v(m_util.fm());
    if (m_util.is_value(arg1, v)) {
        result = (m_util.fm().is_nzero(v)) ? m().mk_true() : m().mk_false();
        return BR_DONE;
    }

    return BR_FAILED;
}

br_status float_rewriter::mk_is_pzero(expr * arg1, expr_ref & result) {
    scoped_mpf v(m_util.fm());
    if (m_util.is_value(arg1, v)) {
        result = (m_util.fm().is_pzero(v)) ? m().mk_true() : m().mk_false();
        return BR_DONE;
    }

    return BR_FAILED;
}

br_status float_rewriter::mk_is_sign_minus(expr * arg1, expr_ref & result) {
    scoped_mpf v(m_util.fm());
    if (m_util.is_value(arg1, v)) {
        result = (m_util.fm().is_neg(v)) ? m().mk_true() : m().mk_false();
        return BR_DONE;
    }

    return BR_FAILED;
}

// This the SMT =
br_status float_rewriter::mk_eq_core(expr * arg1, expr * arg2, expr_ref & result) {
    scoped_mpf v1(m_util.fm()), v2(m_util.fm());
    if (m_util.is_value(arg1, v1) && m_util.is_value(arg2, v2)) {
        result = (v1 == v2) ? m().mk_true() : m().mk_false();
        return BR_DONE;
    }

    return BR_FAILED;
}
