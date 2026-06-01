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
#include "params/fpa_rewriter_params.hpp"
#include "ast/ast_smt2_pp.h"

fpa_rewriter::fpa_rewriter(ast_manager & m, params_ref const & p) :
    m_util(m),
    m_fm(m_util.fm()),
    m_hi_fp_unspecified(false) {
    updt_params(p);
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
    case OP_FPA_MIN_I:     SASSERT(num_args == 2); st = mk_min(args[0], args[1], result); break;
    case OP_FPA_MAX_I:     SASSERT(num_args == 2); st = mk_max(args[0], args[1], result); break;
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
    case OP_FPA_TO_UBV:     SASSERT(num_args == 2); st = mk_to_ubv(f, args[0], args[1], result); break;
    case OP_FPA_TO_SBV:     SASSERT(num_args == 2); st = mk_to_sbv(f, args[0], args[1], result); break;
    case OP_FPA_TO_UBV_I:   SASSERT(num_args == 2); st = mk_to_ubv(f, args[0], args[1], result); break;
    case OP_FPA_TO_SBV_I:   SASSERT(num_args == 2); st = mk_to_sbv(f, args[0], args[1], result); break;
    case OP_FPA_TO_IEEE_BV: SASSERT(num_args == 1); st = mk_to_ieee_bv(f, args[0], result); break;
    case OP_FPA_TO_IEEE_BV_I: SASSERT(num_args == 1); st = mk_to_ieee_bv(f, args[0], result); break;
    case OP_FPA_TO_REAL:   SASSERT(num_args == 1); st = mk_to_real(args[0], result); break;
    case OP_FPA_TO_REAL_I:   SASSERT(num_args == 1); st = mk_to_real(args[0], result); break;

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
            TRACE(fp_rewriter,
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
            TRACE(fp_rewriter, tout << "r: " << r1 << std::endl;);
            scoped_mpf v(m_fm);
            m_fm.set(v, ebits, sbits, rmv, r1.to_mpq());
            result = m_util.mk_value(v);
            // TRACE(fp_rewriter, tout << "result: " << result << std::endl; );
            return BR_DONE;
        }
        else if (m_util.is_numeral(args[1], v)) {
            // rm + float -> float
            TRACE(fp_rewriter, tout << "v: " << m_fm.to_string(v) << std::endl; );
            scoped_mpf vf(m_fm);
            m_fm.set(vf, ebits, sbits, rmv, v);
            result = m_util.mk_value(vf);
            // TRACE(fp_rewriter, tout << "result: " << result << std::endl; );
            return BR_DONE;
        }
        else if (m_util.bu().is_numeral(args[1], r1, bvs1)) {
            // rm + signed bv -> float
            TRACE(fp_rewriter, tout << "r1: " << r1 << std::endl;);
            r1 = m_util.bu().norm(r1, bvs1, true);
            TRACE(fp_rewriter, tout << "r1 norm: " << r1 << std::endl;);
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

            TRACE(fp_rewriter, tout << "r1: " << r1 << ", r2: " << r2 << "\n";);
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

            TRACE(fp_rewriter, tout << "r1: " << r1 << ", r2: " << r2 << "\n";);
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
            TRACE(fp_rewriter, tout << "v = " << m_fm.to_string(v) << std::endl;);
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
        result = m_util.mk_ninf(arg1->get_sort());
        return BR_DONE;
    }
    if (m_util.is_ninf(arg1)) {
        // - -oo -> +oo
        result = m_util.mk_pinf(arg1->get_sort());
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

        // fma(rm, ±0, y, z) or fma(rm, x, ±0, z): when one multiplicand is
        // a concrete zero the full FMA bit-blast circuit is unnecessary.
        // IEEE 754: 0 * finite = ±0, so fma reduces to fp.add(rm, ±0, z).
        //           0 * NaN = NaN, 0 * inf = NaN.
        expr *other_mul = nullptr;
        bool zero_is_neg = false;
        scoped_mpf vzero(m_fm);
        if (m_util.is_numeral(arg2, vzero) && m_fm.is_zero(vzero)) {
            other_mul = arg3;
            zero_is_neg = m_fm.is_neg(vzero);
        }
        else {
            scoped_mpf v3tmp(m_fm);
            if (m_util.is_numeral(arg3, v3tmp) && m_fm.is_zero(v3tmp)) {
                other_mul = arg2;
                zero_is_neg = m_fm.is_neg(v3tmp);
                m_fm.set(vzero, v3tmp);
            }
        }

        if (other_mul) {
            TRACE(fp_rewriter, tout << "fma zero-multiplicand simplification\n";);
            sort *s = arg4->get_sort();
            expr_ref nan(m_util.mk_nan(s), m());

            // fma(rm, ±0, y, NaN) = NaN
            if (m_util.is_nan(arg4)) {
                result = nan;
                return BR_DONE;
            }

            // If the other multiplicand is a concrete NaN or infinity, result is NaN
            scoped_mpf vo(m_fm);
            if (m_util.is_numeral(other_mul, vo) && (m_fm.is_nan(vo) || m_fm.is_inf(vo))) {
                result = nan;
                return BR_DONE;
            }

            // If the other multiplicand is concrete and finite, compute the product
            // ±0, which is exact, then rewrite to fp.add(rm, product, z)
            if (m_util.is_numeral(other_mul, vo)) {
                scoped_mpf product(m_fm);
                m_fm.mul(rm, vzero, vo, product);
                SASSERT(m_fm.is_zero(product));
                result = m_util.mk_add(arg1, m_util.mk_value(product), arg4);
                return BR_REWRITE2;
            }

            // other_mul is symbolic.
            // When z is a concrete non-zero non-NaN value, ±0 + z = z exactly,
            // so fma(rm, ±0, y, z_const) = ite(not isNaN(y) and not isInf(y), z_const, NaN)
            scoped_mpf vz(m_fm);
            if (m_util.is_numeral(arg4, vz) && !m_fm.is_zero(vz) && !m_fm.is_nan(vz)) {
                expr_ref finite_cond(m());
                finite_cond = m().mk_not(m().mk_or(m_util.mk_is_nan(other_mul),
                                                   m_util.mk_is_inf(other_mul)));
                result = m().mk_ite(finite_cond, arg4, nan);
                return BR_REWRITE_FULL;
            }

            // General case: decompose fma into ite + fp.add, avoiding
            // the expensive FMA bit-blast.
            // product sign = sign(zero) XOR sign(other_mul)
            expr_ref pzero(m_util.mk_pzero(s), m());
            expr_ref nzero(m_util.mk_nzero(s), m());
            expr_ref product_zero(m());
            if (zero_is_neg)
                product_zero = m().mk_ite(m_util.mk_is_negative(other_mul), pzero, nzero);
            else
                product_zero = m().mk_ite(m_util.mk_is_negative(other_mul), nzero, pzero);

            expr_ref finite_cond(m());
            finite_cond = m().mk_not(m().mk_or(m_util.mk_is_nan(other_mul),
                                               m_util.mk_is_inf(other_mul)));
            result = m().mk_ite(finite_cond,
                                m_util.mk_add(arg1, product_zero, arg4),
                                nan);
            return BR_REWRITE_FULL;
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
    return m().mk_eq(arg, m_util.mk_nan(arg->get_sort()));
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

    // isNaN(to_fp(rm, real_or_int)) is always false:
    // converting a real/int value never produces NaN.
    if (m_util.is_to_fp(arg1)) {
        app * a = to_app(arg1);
        if (a->get_num_args() == 2 &&
            (m_util.au().is_real(a->get_arg(1)) ||
             m_util.au().is_int(a->get_arg(1)))) {
            result = m().mk_false();
            return BR_DONE;
        }
    }

    // Push through ite when both branches are concrete FP numerals.
    expr *c = nullptr, *t = nullptr, *e = nullptr;
    if (m().is_ite(arg1, c, t, e)) {
        scoped_mpf vt(m_fm), ve(m_fm);
        if (m_util.is_numeral(t, vt) && m_util.is_numeral(e, ve)) {
            result = m().mk_ite(c,
                m_fm.is_nan(vt) ? m().mk_true() : m().mk_false(),
                m_fm.is_nan(ve) ? m().mk_true() : m().mk_false());
            return BR_REWRITE2;
        }
    }

    return BR_FAILED;
}

br_status fpa_rewriter::mk_is_inf(expr * arg1, expr_ref & result) {
    scoped_mpf v(m_fm);

    if (m_util.is_numeral(arg1, v)) {
        result = (m_fm.is_inf(v)) ? m().mk_true() : m().mk_false();
        return BR_DONE;
    }

    // isInf(to_fp(rm, to_real(int))) → integer overflow condition.
    // Converting a real never produces NaN, and for an integer source,
    // overflow to ±infinity depends only on the magnitude and rounding mode.
    mpf_rounding_mode rm;
    if (m_util.is_to_fp(arg1)) {
        app * a = to_app(arg1);
        if (a->get_num_args() == 2 && m_util.is_rm_numeral(a->get_arg(0), rm)) {
            expr * inner = a->get_arg(1);
            expr * int_expr = nullptr;
            // Detect to_real(int_expr)
            if (m_util.au().is_to_real(inner)) {
                expr * unwrapped = to_app(inner)->get_arg(0);
                if (m_util.au().is_int(unwrapped))
                    int_expr = unwrapped;
            }
            else if (m_util.au().is_int(inner))
                int_expr = inner;

            if (int_expr) {
                func_decl * fd = a->get_decl();
                unsigned ebits = fd->get_parameter(0).get_int();
                unsigned sbits = fd->get_parameter(1).get_int();
                result = mk_is_inf_of_int(rm, ebits, sbits, int_expr);
                if (result)
                    return BR_REWRITE_FULL;
            }
        }
    }

    // isInf(to_fp(rm, real_or_int)) where input is a real: never NaN,
    // but we can't determine finiteness without knowing the real value.

    // Push through ite when both branches are concrete FP numerals.
    expr *c = nullptr, *t = nullptr, *e = nullptr;
    if (m().is_ite(arg1, c, t, e)) {
        scoped_mpf vt(m_fm), ve(m_fm);
        if (m_util.is_numeral(t, vt) && m_util.is_numeral(e, ve)) {
            result = m().mk_ite(c,
                m_fm.is_inf(vt) ? m().mk_true() : m().mk_false(),
                m_fm.is_inf(ve) ? m().mk_true() : m().mk_false());
            return BR_REWRITE2;
        }
    }

    return BR_FAILED;
}

br_status fpa_rewriter::mk_is_normal(expr * arg1, expr_ref & result) {
    scoped_mpf v(m_fm);

    if (m_util.is_numeral(arg1, v)) {
        result = (m_fm.is_normal(v)) ? m().mk_true() : m().mk_false();
        return BR_DONE;
    }

    // isNormal(to_fp(rm, to_real(int_expr))) → int_expr ≠ 0 ∧ ¬isInf(to_fp(...))
    // For integer x: to_fp is never NaN or subnormal, so
    // isNormal ↔ x ≠ 0 ∧ ¬overflow(x)
    mpf_rounding_mode rm;
    if (m_util.is_to_fp(arg1)) {
        app * a = to_app(arg1);
        if (a->get_num_args() == 2 && m_util.is_rm_numeral(a->get_arg(0), rm)) {
            expr * inner = a->get_arg(1);
            expr * int_expr = nullptr;
            if (m_util.au().is_to_real(inner)) {
                expr * unwrapped = to_app(inner)->get_arg(0);
                if (m_util.au().is_int(unwrapped))
                    int_expr = unwrapped;
            }
            else if (m_util.au().is_int(inner))
                int_expr = inner;

            if (int_expr) {
                func_decl * fd = a->get_decl();
                unsigned ebits = fd->get_parameter(0).get_int();
                unsigned sbits = fd->get_parameter(1).get_int();
                arith_util & au = m_util.au();
                expr_ref not_zero(m().mk_not(m().mk_eq(int_expr, au.mk_int(0))), m());
                expr_ref inf_cond = mk_is_inf_of_int(rm, ebits, sbits, int_expr);
                result = m().mk_and(not_zero, m().mk_not(inf_cond));
                return BR_REWRITE_FULL;
            }
        }
    }

    // Push through ite when both branches are concrete FP numerals.
    expr *c = nullptr, *t = nullptr, *e = nullptr;
    if (m().is_ite(arg1, c, t, e)) {
        scoped_mpf vt(m_fm), ve(m_fm);
        if (m_util.is_numeral(t, vt) && m_util.is_numeral(e, ve)) {
            result = m().mk_ite(c,
                m_fm.is_normal(vt) ? m().mk_true() : m().mk_false(),
                m_fm.is_normal(ve) ? m().mk_true() : m().mk_false());
            return BR_REWRITE2;
        }
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
        TRACE(fp_rewriter, tout << "simplified (fp ...) to " << m_fm.to_string(v) << std::endl;);
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
    TRACE(fp_rewriter, tout << "to_ieee_bv of " << mk_ismt2_pp(arg, m()) << std::endl;);
    scoped_mpf v(m_fm);

    if (m_util.is_numeral(arg, v)) {
        TRACE(fp_rewriter, tout << "to_ieee_bv numeral: " << m_fm.to_string(v) << std::endl;);
        bv_util bu(m());
        const mpf & x = v.get();

        if (m_fm.is_nan(v)) {
            if (m_hi_fp_unspecified) {
                result = bu.mk_concat({bu.mk_numeral(0, 1),
                                       bu.mk_numeral(rational::minus_one(), x.get_ebits()),
                                       bu.mk_numeral(0, x.get_sbits() - 2),
                                       bu.mk_numeral(1, 1)});
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

// Compute isInf(to_fp(rm, to_real(x))) as an integer constraint on x.
// For integer x, to_fp(rm, x) can only be ±0, normal, or ±infinity, never NaN or subnormal.
// The overflow boundary depends on the rounding mode and float format.
expr_ref fpa_rewriter::mk_is_inf_of_int(mpf_rounding_mode rm, unsigned ebits, unsigned sbits, expr * int_expr) {
    arith_util & au = m_util.au();

    // Compute MAX_FINITE as a rational
    scoped_mpf max_val(m_fm);
    m_fm.mk_max_value(ebits, sbits, false, max_val);
    scoped_mpq max_q(m_fm.mpq_manager());
    m_fm.to_rational(max_val, max_q);
    rational max_finite(max_q);

    // ULP at MAX_FINITE = 2^(max_exp - sbits + 1)
    mpf_exp_t max_exp = m_fm.mk_max_exp(ebits);
    int ulp_exp = (int)max_exp - (int)sbits + 1;
    rational half_ulp = rational::power_of_two(ulp_exp) / rational(2);

    expr_ref r(m());

    switch (rm) {
    case MPF_ROUND_NEAREST_TEVEN:
    case MPF_ROUND_NEAREST_TAWAY: {
        // Overflow when |x| >= MAX_FINITE + ULP/2.
        // At the midpoint, RNE rounds to even, which is infinity since
        // MAX_FINITE has an odd significand. RNA also rounds to infinity.
        rational threshold = max_finite + half_ulp;
        expr_ref thr(au.mk_int(threshold), m());
        expr_ref neg_thr(au.mk_int(-threshold), m());
        // |x| >= threshold  ↔  x >= threshold || x <= -threshold
        r = m().mk_or(au.mk_ge(int_expr, thr), au.mk_le(int_expr, neg_thr));
        break;
    }
    case MPF_ROUND_TOWARD_POSITIVE:
        // RTP: positive overflow when x > MAX_FINITE, negative overflow never.
        r = au.mk_gt(int_expr, au.mk_int(max_finite));
        break;
    case MPF_ROUND_TOWARD_NEGATIVE:
        // RTN: negative overflow when x < -MAX_FINITE, positive overflow never.
        r = au.mk_lt(int_expr, au.mk_int(-max_finite));
        break;
    case MPF_ROUND_TOWARD_ZERO:
        // RTZ: never overflows to infinity from finite input.
        r = m().mk_false();
        break;
    }

    TRACE(fp_rewriter, tout << "isInf(to_fp(rm, int)) -> " << mk_ismt2_pp(r, m()) << "\n";);
    return r;
}
