/*++
Copyright (c) 2012 Microsoft Corporation

Module Name:

    fpa_rewriter.cpp

Abstract:

    Basic rewriting rules for floating point numbers.

Author:

    Leonardo (leonardo) 2012-02-02

Notes:

--*/
#include "ast/rewriter/fpa_rewriter.h"
#include "ast/rewriter/fpa_rewriter_params.hpp"
#include "ast/ast_smt2_pp.h"

fpa_rewriter::fpa_rewriter(ast_manager & m, params_ref const & p) :
    m_util(m),
    m_fm(m_util.fm()),
    m_hi_fp_unspecified(false) {
    updt_params(p);
}

fpa_rewriter::~fpa_rewriter() {
}

void fpa_rewriter::updt_params(params_ref const & _p) {
    fpa_rewriter_params p(_p);
    m_hi_fp_unspecified = p.hi_fp_unspecified();
}

void fpa_rewriter::get_param_descrs(param_descrs & r) {
}

br_status fpa_rewriter::mk_app_core(func_decl * f, unsigned num_args, expr * const * args, expr_ref & result) {
    br_status st = BR_FAILED;
    SASSERT(f->get_family_id() == get_fid());
    fpa_op_kind k = (fpa_op_kind)f->get_decl_kind();
    switch (k) {
    case OP_FPA_RM_NEAREST_TIES_TO_EVEN:
    case OP_FPA_RM_NEAREST_TIES_TO_AWAY:
    case OP_FPA_RM_TOWARD_POSITIVE:
    case OP_FPA_RM_TOWARD_NEGATIVE:
    case OP_FPA_RM_TOWARD_ZERO:
        SASSERT(num_args == 0); result = m().mk_app(f, (expr * const *)nullptr); st = BR_DONE; break;

    case OP_FPA_PLUS_INF:
    case OP_FPA_MINUS_INF:
    case OP_FPA_NAN:
    case OP_FPA_PLUS_ZERO:
    case OP_FPA_MINUS_ZERO:
        SASSERT(num_args == 0); result = m().mk_app(f, (expr * const *)nullptr); st = BR_DONE; break;

    case OP_FPA_NUM:
        SASSERT(num_args == 0); result = m().mk_app(f, (expr * const *)nullptr); st = BR_DONE; break;

    case OP_FPA_ADD:       SASSERT(num_args == 3); st = mk_add(args[0], args[1], args[2], result); break;
    case OP_FPA_SUB:       SASSERT(num_args == 3); st = mk_sub(args[0], args[1], args[2], result); break;
    case OP_FPA_NEG:       SASSERT(num_args == 1); st = mk_neg(args[0], result); break;
    case OP_FPA_MUL:       SASSERT(num_args == 3); st = mk_mul(args[0], args[1], args[2], result); break;
    case OP_FPA_DIV:       SASSERT(num_args == 3); st = mk_div(args[0], args[1], args[2], result); break;
    case OP_FPA_REM:       SASSERT(num_args == 2); st = mk_rem(args[0], args[1], result); break;
    case OP_FPA_ABS:       SASSERT(num_args == 1); st = mk_abs(args[0], result); break;
    case OP_FPA_MIN:       SASSERT(num_args == 2); st = mk_min(args[0], args[1], result); break;
    case OP_FPA_MAX:       SASSERT(num_args == 2); st = mk_max(args[0], args[1], result); break;
    case OP_FPA_FMA:       SASSERT(num_args == 4); st = mk_fma(args[0], args[1], args[2], args[3], result); break;
    case OP_FPA_SQRT:      SASSERT(num_args == 2); st = mk_sqrt(args[0], args[1], result); break;
    case OP_FPA_ROUND_TO_INTEGRAL: SASSERT(num_args == 2); st = mk_round_to_integral(args[0], args[1], result); break;

    case OP_FPA_EQ:        SASSERT(num_args == 2); st = mk_float_eq(args[0], args[1], result); break;
    case OP_FPA_LT:        SASSERT(num_args == 2); st = mk_lt(args[0], args[1], result); break;
    case OP_FPA_GT:        SASSERT(num_args == 2); st = mk_gt(args[0], args[1], result); break;
    case OP_FPA_LE:        SASSERT(num_args == 2); st = mk_le(args[0], args[1], result); break;
    case OP_FPA_GE:        SASSERT(num_args == 2); st = mk_ge(args[0], args[1], result); break;
    case OP_FPA_IS_ZERO:   SASSERT(num_args == 1); st = mk_is_zero(args[0], result); break;
    case OP_FPA_IS_NAN:    SASSERT(num_args == 1); st = mk_is_nan(args[0], result); break;
    case OP_FPA_IS_INF:    SASSERT(num_args == 1); st = mk_is_inf(args[0], result); break;
    case OP_FPA_IS_NORMAL: SASSERT(num_args == 1); st = mk_is_normal(args[0], result); break;
    case OP_FPA_IS_SUBNORMAL: SASSERT(num_args == 1); st = mk_is_subnormal(args[0], result); break;
    case OP_FPA_IS_NEGATIVE: SASSERT(num_args == 1); st = mk_is_negative(args[0], result); break;
    case OP_FPA_IS_POSITIVE: SASSERT(num_args == 1); st = mk_is_positive(args[0], result); break;

    case OP_FPA_FP:        SASSERT(num_args == 3); st = mk_fp(args[0], args[1], args[2], result); break;
    case OP_FPA_TO_FP:     st = mk_to_fp(f, num_args, args, result); break;
    case OP_FPA_TO_FP_UNSIGNED: SASSERT(num_args == 2); st = mk_to_fp_unsigned(f, args[0], args[1], result); break;
    case OP_FPA_TO_UBV:    SASSERT(num_args == 2); st = mk_to_ubv(f, args[0], args[1], result); break;
    case OP_FPA_TO_SBV:    SASSERT(num_args == 2); st = mk_to_sbv(f, args[0], args[1], result); break;
    case OP_FPA_TO_IEEE_BV: SASSERT(num_args == 1); st = mk_to_ieee_bv(f, args[0], result); break;
    case OP_FPA_TO_REAL:   SASSERT(num_args == 1); st = mk_to_real(args[0], result); break;

    case OP_FPA_BVWRAP: SASSERT(num_args == 1); st = mk_bvwrap(args[0], result); break;
    case OP_FPA_BV2RM: SASSERT(num_args == 1); st = mk_bv2rm(args[0], result); break;

    default:
        NOT_IMPLEMENTED_YET();
    }
    return st;
}

br_status fpa_rewriter::mk_to_fp(func_decl * f, unsigned num_args, expr * const * args, expr_ref & result) {
    SASSERT(f->get_num_parameters() == 2);
    SASSERT(f->get_parameter(0).is_int());
    SASSERT(f->get_parameter(1).is_int());
    scoped_mpf v(m_fm);
    mpf_rounding_mode rmv;
    rational r1, r2, r3;
    unsigned bvs1, bvs2, bvs3;
    unsigned ebits = f->get_parameter(0).get_int();
    unsigned sbits = f->get_parameter(1).get_int();

    if (num_args == 1) {
        if (m_util.bu().is_numeral(args[0], r1, bvs1)) {
            // BV -> float
            SASSERT(bvs1 == sbits + ebits);
            unsynch_mpz_manager & mpzm = m_fm.mpz_manager();
            scoped_mpz sig(mpzm), exp(mpzm);

            const mpz & sm1 = m_fm.m_powers2(sbits - 1);
            const mpz & em1 = m_fm.m_powers2(ebits);

            const mpq & q = r1.to_mpq();
            SASSERT(mpzm.is_one(q.denominator()));
            scoped_mpz z(mpzm);
            z = q.numerator();

            mpzm.rem(z, sm1, sig);
            mpzm.div(z, sm1, z);

            mpzm.rem(z, em1, exp);
            mpzm.div(z, em1, z);

            SASSERT(mpzm.is_int64(exp));
            mpf_exp_t mpf_exp = mpzm.get_int64(exp);
            mpf_exp = m_fm.unbias_exp(ebits, mpf_exp);

            m_fm.set(v, ebits, sbits, !mpzm.is_zero(z), mpf_exp, sig);
            TRACE("fp_rewriter",
                  tout << "sgn: " << !mpzm.is_zero(z) << std::endl;
                  tout << "sig: " << mpzm.to_string(sig) << std::endl;
                  tout << "exp: " << mpf_exp << std::endl;
                  tout << "v: " << m_fm.to_string(v) << std::endl;);

            result = m_util.mk_value(v);
            return BR_DONE;
        }
    }
    else if (num_args == 2) {
        if (!m_util.is_rm_numeral(args[0], rmv))
            return BR_FAILED;

        if (m_util.au().is_numeral(args[1], r1)) {
            // rm + real -> float
            TRACE("fp_rewriter", tout << "r: " << r1 << std::endl;);
            scoped_mpf v(m_fm);
            m_fm.set(v, ebits, sbits, rmv, r1.to_mpq());
            result = m_util.mk_value(v);
            // TRACE("fp_rewriter", tout << "result: " << result << std::endl; );
            return BR_DONE;
        }
        else if (m_util.is_numeral(args[1], v)) {
            // rm + float -> float
            TRACE("fp_rewriter", tout << "v: " << m_fm.to_string(v) << std::endl; );
            scoped_mpf vf(m_fm);
            m_fm.set(vf, ebits, sbits, rmv, v);
            result = m_util.mk_value(vf);
            // TRACE("fp_rewriter", tout << "result: " << result << std::endl; );
            return BR_DONE;
        }
        else if (m_util.bu().is_numeral(args[1], r1, bvs1)) {
            // rm + signed bv -> float
            TRACE("fp_rewriter", tout << "r1: " << r1 << std::endl;);
            r1 = m_util.bu().norm(r1, bvs1, true);
            TRACE("fp_rewriter", tout << "r1 norm: " << r1 << std::endl;);
            m_fm.set(v, ebits, sbits, rmv, r1.to_mpq());
            result = m_util.mk_value(v);
            return BR_DONE;
        }
    }
    else if (num_args == 3) {
        if (m_util.is_rm_numeral(args[0], rmv) &&
            m_util.au().is_real(args[1]) &&
            m_util.au().is_int(args[2])) {
            // rm + real + int -> float
            if (!m_util.is_rm_numeral(args[0], rmv) ||
                !m_util.au().is_numeral(args[1], r1) ||
                !m_util.au().is_numeral(args[2], r2))
                return BR_FAILED;

            TRACE("fp_rewriter", tout << "r1: " << r1 << ", r2: " << r2 << "\n";);
            m_fm.set(v, ebits, sbits, rmv, r2.to_mpq().numerator(), r1.to_mpq());
            result = m_util.mk_value(v);
            return BR_DONE;
        }
        else if (m_util.is_rm_numeral(args[0], rmv) &&
                 m_util.au().is_int(args[1]) &&
                 m_util.au().is_real(args[2])) {
            // rm + int + real -> float
            if (!m_util.is_rm_numeral(args[0], rmv) ||
                !m_util.au().is_numeral(args[1], r1) ||
                !m_util.au().is_numeral(args[2], r2))
                return BR_FAILED;

            TRACE("fp_rewriter", tout << "r1: " << r1 << ", r2: " << r2 << "\n";);
            m_fm.set(v, ebits, sbits, rmv, r1.to_mpq().numerator(), r2.to_mpq());
            result = m_util.mk_value(v);
            return BR_DONE;
        }
        else if (m_util.bu().is_numeral(args[0], r1, bvs1) &&
                 m_util.bu().is_numeral(args[1], r2, bvs2) &&
                 m_util.bu().is_numeral(args[2], r3, bvs3)) {
            // 3 BV -> float
            SASSERT(m_fm.mpz_manager().is_one(r2.to_mpq().denominator()));
            SASSERT(m_fm.mpz_manager().is_one(r3.to_mpq().denominator()));
            SASSERT(m_fm.mpz_manager().is_int64(r3.to_mpq().numerator()));
            mpf_exp_t biased_exp = m_fm.mpz_manager().get_int64(r2.to_mpq().numerator());
            m_fm.set(v, bvs2, bvs3 + 1,
                            r1.is_one(),
                            m_fm.unbias_exp(bvs2, biased_exp),
                            r3.to_mpq().numerator());
            TRACE("fp_rewriter", tout << "v = " << m_fm.to_string(v) << std::endl;);
            result = m_util.mk_value(v);
            return BR_DONE;
        }
    }

    return BR_FAILED;
}

br_status fpa_rewriter::mk_to_fp_unsigned(func_decl * f, expr * arg1, expr * arg2, expr_ref & result) {
    SASSERT(f->get_num_parameters() == 2);
    SASSERT(f->get_parameter(0).is_int());
    SASSERT(f->get_parameter(1).is_int());
    unsigned ebits = f->get_parameter(0).get_int();
    unsigned sbits = f->get_parameter(1).get_int();
    mpf_rounding_mode rmv;
    rational r;
    unsigned bvs;

    if (m_util.is_rm_numeral(arg1, rmv) &&
        m_util.bu().is_numeral(arg2, r, bvs)) {
        scoped_mpf v(m_fm);
        m_fm.set(v, ebits, sbits, rmv, r.to_mpq());
        result = m_util.mk_value(v);
        return BR_DONE;
    }

    return BR_FAILED;
}

br_status fpa_rewriter::mk_add(expr * arg1, expr * arg2, expr * arg3, expr_ref & result) {
    mpf_rounding_mode rm;
    if (m_util.is_rm_numeral(arg1, rm)) {
        scoped_mpf v2(m_fm), v3(m_fm);
        if (m_util.is_numeral(arg2, v2) && m_util.is_numeral(arg3, v3)) {
            scoped_mpf t(m_fm);
            m_fm.add(rm, v2, v3, t);
            result = m_util.mk_value(t);
            return BR_DONE;
        }
    }

    return BR_FAILED;
}

br_status fpa_rewriter::mk_sub(expr * arg1, expr * arg2, expr * arg3, expr_ref & result) {
    // a - b = a + (-b)
    result = m_util.mk_add(arg1, arg2, m_util.mk_neg(arg3));
    return BR_REWRITE2;
}

br_status fpa_rewriter::mk_mul(expr * arg1, expr * arg2, expr * arg3, expr_ref & result) {
    mpf_rounding_mode rm;

    if (m_util.is_rm_numeral(arg1, rm)) {
        scoped_mpf v2(m_fm), v3(m_fm);
        if (m_util.is_numeral(arg2, v2) && m_util.is_numeral(arg3, v3)) {
            scoped_mpf t(m_fm);
            m_fm.mul(rm, v2, v3, t);
            result = m_util.mk_value(t);
            return BR_DONE;
        }
    }

    return BR_FAILED;
}

br_status fpa_rewriter::mk_div(expr * arg1, expr * arg2, expr * arg3, expr_ref & result) {
    mpf_rounding_mode rm;

    if (m_util.is_rm_numeral(arg1, rm)) {
        scoped_mpf v2(m_fm), v3(m_fm);
        if (m_util.is_numeral(arg2, v2) && m_util.is_numeral(arg3, v3)) {
            scoped_mpf t(m_fm);
            m_fm.div(rm, v2, v3, t);
            result = m_util.mk_value(t);
            return BR_DONE;
        }
    }
    return BR_FAILED;
}

br_status fpa_rewriter::mk_neg(expr * arg1, expr_ref & result) {
    if (m_util.is_nan(arg1)) {
        // -nan --> nan
        result = arg1;
        return BR_DONE;
    }
    if (m_util.is_pinf(arg1)) {
        // - +oo --> -oo
        result = m_util.mk_ninf(m().get_sort(arg1));
        return BR_DONE;
    }
    if (m_util.is_ninf(arg1)) {
        // - -oo -> +oo
        result = m_util.mk_pinf(m().get_sort(arg1));
        return BR_DONE;
    }
    if (m_util.is_neg(arg1)) {
        // - - a --> a
        result = to_app(arg1)->get_arg(0);
        return BR_DONE;
    }

    scoped_mpf v1(m_fm);
    if (m_util.is_numeral(arg1, v1)) {
        m_fm.neg(v1);
        result = m_util.mk_value(v1);
        return BR_DONE;
    }

    return BR_FAILED;
}

br_status fpa_rewriter::mk_rem(expr * arg1, expr * arg2, expr_ref & result) {
    scoped_mpf v1(m_fm), v2(m_fm);

    if (m_util.is_numeral(arg1, v1) && m_util.is_numeral(arg2, v2)) {
        scoped_mpf t(m_fm);
        m_fm.rem(v1, v2, t);
        result = m_util.mk_value(t);
        return BR_DONE;
    }

    return BR_FAILED;
}

br_status fpa_rewriter::mk_abs(expr * arg1, expr_ref & result) {
    if (m_util.is_nan(arg1)) {
        result = arg1;
        return BR_DONE;
    }

    scoped_mpf v(m_fm);
    if (m_util.is_numeral(arg1, v)) {
        if (m_fm.is_neg(v)) m_fm.neg(v);
        result = m_util.mk_value(v);
        return BR_DONE;
    }

    return BR_FAILED;
}

br_status fpa_rewriter::mk_min(expr * arg1, expr * arg2, expr_ref & result) {
    if (m_util.is_nan(arg1)) {
        result = arg2;
        return BR_DONE;
    }
    else if (m_util.is_nan(arg2)) {
        result = arg1;
        return BR_DONE;
    }

    scoped_mpf v1(m_fm), v2(m_fm);
    if (m_util.is_numeral(arg1, v1) && m_util.is_numeral(arg2, v2)) {
        if (m_fm.is_zero(v1) && m_fm.is_zero(v2) && m_fm.sgn(v1) != m_fm.sgn(v2))
            return BR_FAILED;

        scoped_mpf r(m_fm);
        m_fm.minimum(v1, v2, r);
        result = m_util.mk_value(r);
        return BR_DONE;
    }

    return BR_FAILED;
}

br_status fpa_rewriter::mk_max(expr * arg1, expr * arg2, expr_ref & result) {
    if (m_util.is_nan(arg1)) {
        result = arg2;
        return BR_DONE;
    }
    else if (m_util.is_nan(arg2)) {
        result = arg1;
        return BR_DONE;
    }

    scoped_mpf v1(m_fm), v2(m_fm);
    if (m_util.is_numeral(arg1, v1) && m_util.is_numeral(arg2, v2)) {
        if (m_fm.is_zero(v1) && m_fm.is_zero(v2) && m_fm.sgn(v1) != m_fm.sgn(v2))
            return BR_FAILED;

        scoped_mpf r(m_fm);
        m_fm.maximum(v1, v2, r);
        result = m_util.mk_value(r);
        return BR_DONE;
    }

    return BR_FAILED;
}

br_status fpa_rewriter::mk_fma(expr * arg1, expr * arg2, expr * arg3, expr * arg4, expr_ref & result) {
    mpf_rounding_mode rm;

    if (m_util.is_rm_numeral(arg1, rm)) {
        scoped_mpf v2(m_fm), v3(m_fm), v4(m_fm);
        if (m_util.is_numeral(arg2, v2) && m_util.is_numeral(arg3, v3) && m_util.is_numeral(arg4, v4)) {
            scoped_mpf t(m_fm);
            m_fm.fma(rm, v2, v3, v4, t);
            result = m_util.mk_value(t);
            return BR_DONE;
        }
    }

    return BR_FAILED;
}

br_status fpa_rewriter::mk_sqrt(expr * arg1, expr * arg2, expr_ref & result) {
    mpf_rounding_mode rm;

    if (m_util.is_rm_numeral(arg1, rm)) {
        scoped_mpf v2(m_fm);
        if (m_util.is_numeral(arg2, v2)) {
            scoped_mpf t(m_fm);
            m_fm.sqrt(rm, v2, t);
            result = m_util.mk_value(t);
            return BR_DONE;
        }
    }

    return BR_FAILED;
}

br_status fpa_rewriter::mk_round_to_integral(expr * arg1, expr * arg2, expr_ref & result) {
    mpf_rounding_mode rm;

    if (m_util.is_rm_numeral(arg1, rm)) {
        scoped_mpf v2(m_fm);
        if (m_util.is_numeral(arg2, v2)) {
            scoped_mpf t(m_fm);
            m_fm.round_to_integral(rm, v2, t);
            result = m_util.mk_value(t);
            return BR_DONE;
        }
    }

    return BR_FAILED;
}

// This the floating point theory ==
br_status fpa_rewriter::mk_float_eq(expr * arg1, expr * arg2, expr_ref & result) {
    scoped_mpf v1(m_fm), v2(m_fm);

    if (m_util.is_numeral(arg1, v1) && m_util.is_numeral(arg2, v2)) {
        result = (m_fm.eq(v1, v2)) ? m().mk_true() : m().mk_false();
        return BR_DONE;
    }

    return BR_FAILED;
}

// Return (= arg NaN)
app * fpa_rewriter::mk_eq_nan(expr * arg) {
    return m().mk_eq(arg, m_util.mk_nan(m().get_sort(arg)));
}

// Return (not (= arg NaN))
app * fpa_rewriter::mk_neq_nan(expr * arg) {
    return m().mk_not(mk_eq_nan(arg));
}

br_status fpa_rewriter::mk_lt(expr * arg1, expr * arg2, expr_ref & result) {
    if (m_util.is_nan(arg1) || m_util.is_nan(arg2)) {
        result = m().mk_false();
        return BR_DONE;
    }
    if (m_util.is_ninf(arg1)) {
        // -oo < arg2 -->  not(arg2 = -oo) and not(arg2 = NaN)
        result = m().mk_and(m().mk_not(m().mk_eq(arg2, arg1)), mk_neq_nan(arg2));
        return BR_REWRITE3;
    }
    if (m_util.is_ninf(arg2)) {
        // arg1 < -oo  --> false
        result = m().mk_false();
        return BR_DONE;
    }
    if (m_util.is_pinf(arg1)) {
        // +oo < arg2 --> false
        result = m().mk_false();
        return BR_DONE;
    }
    if (m_util.is_pinf(arg2)) {
        // arg1 < +oo --> not(arg1 = +oo) and not(arg1 = NaN)
        result = m().mk_and(m().mk_not(m().mk_eq(arg1, arg2)), mk_neq_nan(arg1));
        return BR_REWRITE3;
    }

    scoped_mpf v1(m_fm), v2(m_fm);
    if (m_util.is_numeral(arg1, v1) && m_util.is_numeral(arg2, v2)) {
        result = (m_fm.lt(v1, v2)) ? m().mk_true() : m().mk_false();
        return BR_DONE;
    }

    return BR_FAILED;
}

br_status fpa_rewriter::mk_gt(expr * arg1, expr * arg2, expr_ref & result) {
    result = m_util.mk_lt(arg2, arg1);
    return BR_REWRITE1;
}

br_status fpa_rewriter::mk_le(expr * arg1, expr * arg2, expr_ref & result) {
    if (m_util.is_nan(arg1) || m_util.is_nan(arg2)) {
        result = m().mk_false();
        return BR_DONE;
    }

    scoped_mpf v1(m_fm), v2(m_fm);
    if (m_util.is_numeral(arg1, v1) && m_util.is_numeral(arg2, v2)) {
        result = (m_fm.le(v1, v2)) ? m().mk_true() : m().mk_false();
        return BR_DONE;
    }

    return BR_FAILED;
}

br_status fpa_rewriter::mk_ge(expr * arg1, expr * arg2, expr_ref & result) {
    result = m_util.mk_le(arg2, arg1);
    return BR_REWRITE1;
}

br_status fpa_rewriter::mk_is_zero(expr * arg1, expr_ref & result) {
    scoped_mpf v(m_fm);

    if (m_util.is_numeral(arg1, v)) {
        result = (m_fm.is_zero(v)) ? m().mk_true() : m().mk_false();
        return BR_DONE;
    }

    return BR_FAILED;
}

br_status fpa_rewriter::mk_is_nzero(expr * arg1, expr_ref & result) {
    scoped_mpf v(m_fm);

    if (m_util.is_numeral(arg1, v)) {
        result = (m_fm.is_nzero(v)) ? m().mk_true() : m().mk_false();
        return BR_DONE;
    }

    return BR_FAILED;
}

br_status fpa_rewriter::mk_is_pzero(expr * arg1, expr_ref & result) {
    scoped_mpf v(m_fm);

    if (m_util.is_numeral(arg1, v)) {
        result = (m_fm.is_pzero(v)) ? m().mk_true() : m().mk_false();
        return BR_DONE;
    }

    return BR_FAILED;
}

br_status fpa_rewriter::mk_is_nan(expr * arg1, expr_ref & result) {
    scoped_mpf v(m_fm);

    if (m_util.is_numeral(arg1, v)) {
        result = (m_fm.is_nan(v)) ? m().mk_true() : m().mk_false();
        return BR_DONE;
    }

    return BR_FAILED;
}

br_status fpa_rewriter::mk_is_inf(expr * arg1, expr_ref & result) {
    scoped_mpf v(m_fm);

    if (m_util.is_numeral(arg1, v)) {
        result = (m_fm.is_inf(v)) ? m().mk_true() : m().mk_false();
        return BR_DONE;
    }

    return BR_FAILED;
}

br_status fpa_rewriter::mk_is_normal(expr * arg1, expr_ref & result) {
    scoped_mpf v(m_fm);

    if (m_util.is_numeral(arg1, v)) {
        result = (m_fm.is_normal(v)) ? m().mk_true() : m().mk_false();
        return BR_DONE;
    }

    return BR_FAILED;
}

br_status fpa_rewriter::mk_is_subnormal(expr * arg1, expr_ref & result) {
    scoped_mpf v(m_fm);

    if (m_util.is_numeral(arg1, v)) {
        result = (m_fm.is_denormal(v)) ? m().mk_true() : m().mk_false();
        return BR_DONE;
    }

    return BR_FAILED;
}

br_status fpa_rewriter::mk_is_negative(expr * arg1, expr_ref & result) {
    scoped_mpf v(m_fm);

    if (m_util.is_numeral(arg1, v)) {
        result = (m_fm.is_neg(v)) ? m().mk_true() : m().mk_false();
        return BR_DONE;
    }

    return BR_FAILED;
}

br_status fpa_rewriter::mk_is_positive(expr * arg1, expr_ref & result) {
    scoped_mpf v(m_fm);

    if (m_util.is_numeral(arg1, v)) {
        result = (m_fm.is_neg(v) || m_fm.is_nan(v)) ? m().mk_false() : m().mk_true();
        return BR_DONE;
    }

    return BR_FAILED;
}


// This the SMT =
br_status fpa_rewriter::mk_eq_core(expr * arg1, expr * arg2, expr_ref & result) {
    scoped_mpf v1(m_fm), v2(m_fm);

    if (m_util.is_numeral(arg1, v1) && m_util.is_numeral(arg2, v2)) {
        // Note: == is the floats-equality, here we need normal equality.
        result = (m_fm.is_nan(v1) && m_fm.is_nan(v2)) ? m().mk_true() :
                 (m_fm.is_zero(v1) && m_fm.is_zero(v2) && m_fm.sgn(v1)!=m_fm.sgn(v2)) ? m().mk_false() :
                 (v1 == v2) ? m().mk_true() :
                 m().mk_false();
        return BR_DONE;
    }

    return BR_FAILED;
}

br_status fpa_rewriter::mk_bv2rm(expr * arg, expr_ref & result) {
    rational bv_val;
    unsigned sz = 0;

    if (m_util.bu().is_numeral(arg, bv_val, sz)) {
        SASSERT(bv_val.is_uint64());
        switch (bv_val.get_uint64()) {
        case BV_RM_TIES_TO_AWAY: result = m_util.mk_round_nearest_ties_to_away(); break;
        case BV_RM_TIES_TO_EVEN: result = m_util.mk_round_nearest_ties_to_even(); break;
        case BV_RM_TO_NEGATIVE: result = m_util.mk_round_toward_negative(); break;
        case BV_RM_TO_POSITIVE: result = m_util.mk_round_toward_positive(); break;
        case BV_RM_TO_ZERO:
        default: result = m_util.mk_round_toward_zero();
        }

        return BR_DONE;
    }

    return BR_FAILED;
}

br_status fpa_rewriter::mk_fp(expr * sgn, expr * exp, expr * sig, expr_ref & result) {
    unsynch_mpz_manager & mpzm = m_fm.mpz_manager();
    rational rsgn, rexp, rsig;
    unsigned bvsz_sgn, bvsz_exp, bvsz_sig;

    if (m_util.bu().is_numeral(sgn, rsgn, bvsz_sgn) &&
        m_util.bu().is_numeral(sig, rsig, bvsz_sig) &&
        m_util.bu().is_numeral(exp, rexp, bvsz_exp)) {
        SASSERT(mpzm.is_one(rexp.to_mpq().denominator()));
        SASSERT(mpzm.is_one(rsig.to_mpq().denominator()));
        scoped_mpf v(m_fm);
        mpf_exp_t biased_exp = mpzm.get_int64(rexp.to_mpq().numerator());
        m_fm.set(v, bvsz_exp, bvsz_sig + 1,
                        rsgn.is_one(),
                        m_fm.unbias_exp(bvsz_exp, biased_exp),
                        rsig.to_mpq().numerator());
        TRACE("fp_rewriter", tout << "simplified (fp ...) to " << m_fm.to_string(v) << std::endl;);
        result = m_util.mk_value(v);
        return BR_DONE;
    }

    return BR_FAILED;
}

br_status fpa_rewriter::mk_to_bv(func_decl * f, expr * arg1, expr * arg2, bool is_signed, expr_ref & result) {
    SASSERT(f->get_num_parameters() == 1);
    SASSERT(f->get_parameter(0).is_int());
    int bv_sz = f->get_parameter(0).get_int();
    mpf_rounding_mode rmv;
    scoped_mpf v(m_fm);

    if (m_util.is_rm_numeral(arg1, rmv) &&
        m_util.is_numeral(arg2, v)) {

        if (m_fm.is_nan(v) || m_fm.is_inf(v))
            return mk_to_bv_unspecified(f, result);

        bv_util bu(m());
        scoped_mpq q(m_fm.mpq_manager());
        m_fm.to_sbv_mpq(rmv, v, q);

        rational r(q);
        rational ul, ll;
        if (!is_signed) {
            ul = m_fm.m_powers2.m1(bv_sz);
            ll = rational(0);
        }
        else {
            ul = m_fm.m_powers2.m1(bv_sz - 1);
            ll = -m_fm.m_powers2(bv_sz - 1);
        }
        if (r >= ll && r <= ul) {
            result = bu.mk_numeral(r, bv_sz);
            return BR_DONE;
        }
        else
            return mk_to_bv_unspecified(f, result);
    }

    return BR_FAILED;
}

br_status fpa_rewriter::mk_to_bv_unspecified(func_decl * f, expr_ref & result) {
    if (m_hi_fp_unspecified) {
        unsigned bv_sz = m_util.bu().get_bv_size(f->get_range());
        result = m_util.bu().mk_numeral(0, bv_sz);
        return BR_DONE;
    }
    else
        return BR_FAILED;
}

br_status fpa_rewriter::mk_to_ubv(func_decl * f, expr * arg1, expr * arg2, expr_ref & result) {
    return mk_to_bv(f, arg1, arg2, false, result);
}

br_status fpa_rewriter::mk_to_sbv(func_decl * f, expr * arg1, expr * arg2, expr_ref & result) {
    return mk_to_bv(f, arg1, arg2, true, result);
}

br_status fpa_rewriter::mk_to_ieee_bv(func_decl * f, expr * arg, expr_ref & result) {
    TRACE("fp_rewriter", tout << "to_ieee_bv of " << mk_ismt2_pp(arg, m()) << std::endl;);
    scoped_mpf v(m_fm);

    if (m_util.is_numeral(arg, v)) {
        TRACE("fp_rewriter", tout << "to_ieee_bv numeral: " << m_fm.to_string(v) << std::endl;);
        bv_util bu(m());
        const mpf & x = v.get();

        if (m_fm.is_nan(v)) {
            if (m_hi_fp_unspecified) {
                expr * args[4] = { bu.mk_numeral(0, 1),
                                   bu.mk_bv_neg(bu.mk_numeral(1, x.get_ebits())),
                                   bu.mk_numeral(0, x.get_sbits() - 2),
                                   bu.mk_numeral(1, 1) };
                result = bu.mk_concat(4, args);
                return BR_REWRITE1;
            }
        }
        else {
            scoped_mpz rz(m_fm.mpq_manager());
            m_fm.to_ieee_bv_mpz(v, rz);
            result = bu.mk_numeral(rational(rz), x.get_ebits() + x.get_sbits());
            return BR_DONE;
        }
    }

    return BR_FAILED;
}

br_status fpa_rewriter::mk_to_real(expr * arg, expr_ref & result) {
    scoped_mpf v(m_fm);

    if (m_util.is_numeral(arg, v)) {
        if (m_fm.is_nan(v) || m_fm.is_inf(v)) {
            if (m_hi_fp_unspecified) {
                result = m_util.au().mk_numeral(rational(0), false);
                return BR_DONE;
            }
        }
        else {
            scoped_mpq r(m_fm.mpq_manager());
            m_fm.to_rational(v, r);
            result = m_util.au().mk_numeral(r.get(), false);
            return BR_DONE;
        }
    }

    return BR_FAILED;
}

br_status fpa_rewriter::mk_bvwrap(expr * arg, expr_ref & result) {
    if (is_app_of(arg, m_util.get_family_id(), OP_FPA_FP)) {
        bv_util bu(m());
        SASSERT(to_app(arg)->get_num_args() == 3);
        sort_ref fpsrt(m());
        fpsrt = to_app(arg)->get_decl()->get_range();
        expr_ref a0(m()), a1(m()), a2(m());
        a0 = to_app(arg)->get_arg(0);
        a1 = to_app(arg)->get_arg(1);
        a2 = to_app(arg)->get_arg(2);
        if (bu.is_extract(a0) && bu.is_extract(a1) && bu.is_extract(a2)) {
            unsigned w0 = bu.get_extract_high(a0) - bu.get_extract_low(a0) + 1;
            unsigned w1 = bu.get_extract_high(a1) - bu.get_extract_low(a1) + 1;
            unsigned w2 = bu.get_extract_high(a2) - bu.get_extract_low(a2) + 1;
            unsigned cw = w0 + w1 + w2;
            if (cw == m_util.get_ebits(fpsrt) + m_util.get_sbits(fpsrt)) {
                expr_ref aa0(m()), aa1(m()), aa2(m());
                aa0 = to_app(a0)->get_arg(0);
                aa1 = to_app(a1)->get_arg(0);
                aa2 = to_app(a2)->get_arg(0);
                if (aa0 == aa1 && aa1 == aa2 && bu.get_bv_size(aa0) == cw) {
                    result = aa0;
                    return BR_DONE;
                }
            }
        }
    }

    return BR_FAILED;
}
