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
    case OP_FLOAT_IS_NAN:    SASSERT(num_args == 1); st = mk_is_nan(args[0], result); break;
    case OP_FLOAT_IS_INF:    SASSERT(num_args == 1); st = mk_is_inf(args[0], result); break;
    case OP_FLOAT_IS_NORMAL: SASSERT(num_args == 1); st = mk_is_normal(args[0], result); break;
    case OP_FLOAT_IS_SUBNORMAL: SASSERT(num_args == 1); st = mk_is_subnormal(args[0], result); break;
    case OP_FLOAT_IS_SIGN_MINUS: SASSERT(num_args == 1); st = mk_is_sign_minus(args[0], result); break;
    case OP_TO_IEEE_BV:      SASSERT(num_args == 1); st = mk_to_ieee_bv(args[0], result); break;
    case OP_FLOAT_FP:        SASSERT(num_args == 3); st = mk_fp(args[0], args[1], args[2], result); break;
    case OP_FLOAT_TO_FP_UNSIGNED: SASSERT(num_args == 2); st = mk_to_fp_unsigned(args[0], args[1], result); break;
    case OP_FLOAT_TO_UBV:    SASSERT(num_args == 2); st = mk_to_ubv(args[0], args[1], result); break;
    case OP_FLOAT_TO_SBV:    SASSERT(num_args == 2); st = mk_to_sbv(args[0], args[1], result); break;
    case OP_FLOAT_TO_REAL:   SASSERT(num_args == 1); st = mk_to_real(args[0], result); break;
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
        if (!m_util.is_rm_value(args[0], rm))
            return BR_FAILED;
        
        rational q;
        mpf q_mpf;
        if (m_util.au().is_numeral(args[1], q)) {        
            TRACE("fp_rewriter", tout << "q: " << q << std::endl; );
            mpf v;
            m_util.fm().set(v, ebits, sbits, rm, q.to_mpq());
            result = m_util.mk_value(v);
            m_util.fm().del(v);
            // TRACE("fp_rewriter", tout << "result: " << result << std::endl; );
            return BR_DONE;
        }
        else if (m_util.is_value(args[1], q_mpf)) {
            TRACE("fp_rewriter", tout << "q: " << m_util.fm().to_string(q_mpf) << std::endl; );
            mpf v;
            m_util.fm().set(v, ebits, sbits, rm, q_mpf);
            result = m_util.mk_value(v);
            m_util.fm().del(v);
            // TRACE("fp_rewriter", tout << "result: " << result << std::endl; );
            return BR_DONE;
        }
        else 
            return BR_FAILED;
    }
    else if (num_args == 3 && 
             m_util.is_rm(args[0]) && 
             m_util.au().is_real(args[1]) &&
             m_util.au().is_int(args[2])) {

        mpf_rounding_mode rm;
        if (!m_util.is_rm_value(args[0], rm))
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
    if (m_util.is_rm_value(arg1, rm)) {
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
    if (m_util.is_rm_value(arg1, rm)) {
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
    if (m_util.is_rm_value(arg1, rm)) {
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
    result = m().mk_ite(m_util.mk_is_sign_minus(arg1),
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
    result = m().mk_ite(m().mk_or(mk_eq_nan(arg1), m().mk_and(m_util.mk_is_zero(arg1), m_util.mk_is_zero(arg2))),
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
    result = m().mk_ite(m().mk_or(mk_eq_nan(arg1), m().mk_and(m_util.mk_is_zero(arg1), m_util.mk_is_zero(arg2))),
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
    if (m_util.is_rm_value(arg1, rm)) {
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
    if (m_util.is_rm_value(arg1, rm)) {
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
    if (m_util.is_rm_value(arg1, rm)) {
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
        return BR_REWRITE3;
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
        return BR_REWRITE3;
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

br_status float_rewriter::mk_is_nan(expr * arg1, expr_ref & result) {
    scoped_mpf v(m_util.fm());
    if (m_util.is_value(arg1, v)) {
        result = (m_util.fm().is_nan(v)) ? m().mk_true() : m().mk_false();
        return BR_DONE;
    }

    return BR_FAILED;
}

br_status float_rewriter::mk_is_inf(expr * arg1, expr_ref & result) {
    scoped_mpf v(m_util.fm());
    if (m_util.is_value(arg1, v)) {
        result = (m_util.fm().is_inf(v)) ? m().mk_true() : m().mk_false();
        return BR_DONE;
    }

    return BR_FAILED;
}

br_status float_rewriter::mk_is_normal(expr * arg1, expr_ref & result) {
    scoped_mpf v(m_util.fm());
    if (m_util.is_value(arg1, v)) {
        result = (m_util.fm().is_normal(v)) ? m().mk_true() : m().mk_false();
        return BR_DONE;
    }

    return BR_FAILED;
}

br_status float_rewriter::mk_is_subnormal(expr * arg1, expr_ref & result) {
    scoped_mpf v(m_util.fm());
    if (m_util.is_value(arg1, v)) {
        result = (m_util.fm().is_denormal(v)) ? m().mk_true() : m().mk_false();
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
        // Note: == is the floats-equality, here we need normal equality.
        result = (m_fm.is_nan(v1) && m_fm.is_nan(v2)) ? m().mk_true() :
                 (m_fm.is_zero(v1) && m_fm.is_zero(v2) && m_fm.sgn(v1)!=m_fm.sgn(v2)) ? m().mk_false() :
                 (v1 == v2) ? m().mk_true() :
                 m().mk_false();
        return BR_DONE;
    }

    return BR_FAILED;
}

br_status float_rewriter::mk_to_ieee_bv(expr * arg1, expr_ref & result) {
    return BR_FAILED;
}

br_status float_rewriter::mk_fp(expr * arg1, expr * arg2, expr * arg3, expr_ref & result) {    
    bv_util bu(m());
    rational r1, r2, r3;
    unsigned bvs1, bvs2, bvs3;

    if (bu.is_numeral(arg1, r1, bvs1) && bu.is_numeral(arg2, r2, bvs2) && bu.is_numeral(arg3, r3, bvs3)) {        
        SASSERT(m_util.fm().mpz_manager().is_one(r2.to_mpq().denominator()));
        SASSERT(m_util.fm().mpz_manager().is_one(r3.to_mpq().denominator()));
        SASSERT(m_util.fm().mpz_manager().is_int64(r3.to_mpq().numerator()));
        scoped_mpf v(m_util.fm());
        mpf_exp_t biased_exp = m_util.fm().mpz_manager().get_int64(r2.to_mpq().numerator());
        m_util.fm().set(v, bvs2, bvs3 + 1,
                        r1.is_one(),
                        r3.to_mpq().numerator(),
                        m_util.fm().unbias_exp(bvs2, biased_exp));
        TRACE("fp_rewriter", tout << "v = " << m_util.fm().to_string(v) << std::endl;);
        result = m_util.mk_value(v);
        return BR_DONE;
    }

    return BR_FAILED;
}

br_status float_rewriter::mk_to_fp_unsigned(expr * arg1, expr * arg2, expr_ref & result) {
    return BR_FAILED;
}

br_status float_rewriter::mk_to_ubv(expr * arg1, expr * arg2, expr_ref & result) {
    return BR_FAILED;
}

br_status float_rewriter::mk_to_sbv(expr * arg1, expr * arg2, expr_ref & result) {
    return BR_FAILED;
}

br_status float_rewriter::mk_to_real(expr * arg1, expr_ref & result) {
    return BR_FAILED;
}