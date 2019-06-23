/*++
Copyright (c) 2011 Microsoft Corporation

Module Name:

    bv_rewriter.cpp

Abstract:

    Basic rewriting rules for bit-vectors

Author:

    Leonardo (leonardo) 2011-04-14

Notes:

--*/
#include "ast/rewriter/bv_rewriter.h"
#include "ast/rewriter/bv_rewriter_params.hpp"
#include "ast/rewriter/poly_rewriter_def.h"
#include "ast/ast_smt2_pp.h"
#include "ast/ast_lt.h"


void bv_rewriter::updt_local_params(params_ref const & _p) {
    bv_rewriter_params p(_p);
    m_hi_div0 = p.hi_div0();
    m_elim_sign_ext = p.elim_sign_ext();
    m_mul2concat = p.mul2concat();
    m_bit2bool = p.bit2bool();
    m_trailing = p.bv_trailing();
    m_urem_simpl = p.bv_urem_simpl();
    m_blast_eq_value = p.blast_eq_value();
    m_split_concat_eq = p.split_concat_eq();
    m_udiv2mul = p.udiv2mul();
    m_bvnot2arith = p.bvnot2arith();
    m_bvnot_simpl = p.bv_not_simpl();
    m_bv_sort_ac = p.bv_sort_ac();
    m_mkbv2num = _p.get_bool("mkbv2num", false);
    m_extract_prop = p.bv_extract_prop();
    m_ite2id = p.bv_ite2id();
    m_le_extra = p.bv_le_extra();
    set_sort_sums(p.bv_sort_ac());
}

void bv_rewriter::updt_params(params_ref const & p) {
    poly_rewriter<bv_rewriter_core>::updt_params(p);
    updt_local_params(p);
}

void bv_rewriter::get_param_descrs(param_descrs & r) {
    poly_rewriter<bv_rewriter_core>::get_param_descrs(r);
    bv_rewriter_params::collect_param_descrs(r);
#ifndef _EXTERNAL_RELEASE
    r.insert("mkbv2num", CPK_BOOL, "(default: false) convert (mkbv [true/false]*) into a numeral");
#endif
}

br_status bv_rewriter::mk_app_core(func_decl * f, unsigned num_args, expr * const * args, expr_ref & result) {
    SASSERT(f->get_family_id() == get_fid());

    switch(f->get_decl_kind()) {
    case OP_BIT0: SASSERT(num_args == 0); result = m_util.mk_numeral(0, 1); return BR_DONE;
    case OP_BIT1: SASSERT(num_args == 0); result = m_util.mk_numeral(1, 1); return BR_DONE;
    case OP_ULEQ:
        SASSERT(num_args == 2);
        return mk_ule(args[0], args[1], result);
    case OP_UGEQ:
        SASSERT(num_args == 2);
        return mk_uge(args[0], args[1], result);
    case OP_ULT:
        SASSERT(num_args == 2);
        return mk_ult(args[0], args[1], result);
    case OP_UGT:
        SASSERT(num_args == 2);
        return mk_ult(args[1], args[0], result);
    case OP_SLEQ:
        SASSERT(num_args == 2);
        return mk_sle(args[0], args[1], result);
    case OP_SGEQ:
        SASSERT(num_args == 2);
        return mk_sge(args[0], args[1], result);
    case OP_SLT:
        SASSERT(num_args == 2);
        return mk_slt(args[0], args[1], result);
    case OP_SGT:
        SASSERT(num_args == 2);
        return mk_slt(args[1], args[0], result);
    case OP_BADD:
        SASSERT(num_args > 0);
        return mk_bv_add(num_args, args, result);
    case OP_BMUL:
        SASSERT(num_args > 0);
        return mk_bv_mul(num_args, args, result);
    case OP_BSUB:
        SASSERT(num_args > 0);
        return mk_sub(num_args, args, result);
    case OP_BNEG:
        SASSERT(num_args == 1);
        return mk_uminus(args[0], result);
    case OP_BSHL:
        SASSERT(num_args == 2);
        return mk_bv_shl(args[0], args[1], result);
    case OP_BLSHR:
        SASSERT(num_args == 2);
        return mk_bv_lshr(args[0], args[1], result);
    case OP_BASHR:
        SASSERT(num_args == 2);
        return mk_bv_ashr(args[0], args[1], result);
    case OP_BSDIV:
        SASSERT(num_args == 2);
        return mk_bv_sdiv(args[0], args[1], result);
    case OP_BUDIV:
        SASSERT(num_args == 2);
        return mk_bv_udiv(args[0], args[1], result);
    case OP_BSREM:
        SASSERT(num_args == 2);
        return mk_bv_srem(args[0], args[1], result);
    case OP_BUREM:
        SASSERT(num_args == 2);
        return mk_bv_urem(args[0], args[1], result);
    case OP_BSMOD:
        SASSERT(num_args == 2);
        return mk_bv_smod(args[0], args[1], result);
    case OP_BSDIV_I:
        SASSERT(num_args == 2);
        return mk_bv_sdiv_i(args[0], args[1], result);
    case OP_BUDIV_I:
        SASSERT(num_args == 2);
        return mk_bv_udiv_i(args[0], args[1], result);
    case OP_BSREM_I:
        SASSERT(num_args == 2);
        return mk_bv_srem_i(args[0], args[1], result);
    case OP_BUREM_I:
        SASSERT(num_args == 2);
        return mk_bv_urem_i(args[0], args[1], result);
    case OP_BSMOD_I:
        SASSERT(num_args == 2);
        return mk_bv_smod_i(args[0], args[1], result);
    case OP_CONCAT:
        return mk_concat(num_args, args, result);
    case OP_EXTRACT:
        SASSERT(num_args == 1);
        return mk_extract(m_util.get_extract_high(f), m_util.get_extract_low(f), args[0], result);
    case OP_REPEAT:
        SASSERT(num_args == 1);
        return mk_repeat(f->get_parameter(0).get_int(), args[0], result);
    case OP_ZERO_EXT:
        SASSERT(num_args == 1);
        return mk_zero_extend(f->get_parameter(0).get_int(), args[0], result);
    case OP_SIGN_EXT:
        SASSERT(num_args == 1);
        return mk_sign_extend(f->get_parameter(0).get_int(), args[0], result);
    case OP_BOR:
        return mk_bv_or(num_args, args, result);
    case OP_BXOR:
        return mk_bv_xor(num_args, args, result);
    case OP_BNOT:
        SASSERT(num_args == 1);
        return mk_bv_not(args[0], result);
    case OP_BAND:
        return mk_bv_and(num_args, args, result);
    case OP_BNAND:
        return mk_bv_nand(num_args, args, result);
    case OP_BNOR:
        return mk_bv_nor(num_args, args, result);
    case OP_BXNOR:
        return mk_bv_xnor(num_args, args, result);
    case OP_ROTATE_LEFT:
        SASSERT(num_args == 1);
        return mk_bv_rotate_left(f->get_parameter(0).get_int(), args[0], result);
    case OP_ROTATE_RIGHT:
        SASSERT(num_args == 1);
        return mk_bv_rotate_right(f->get_parameter(0).get_int(), args[0], result);
    case OP_EXT_ROTATE_LEFT:
        SASSERT(num_args == 2);
        return mk_bv_ext_rotate_left(args[0], args[1], result);
    case OP_EXT_ROTATE_RIGHT:
        SASSERT(num_args == 2);
        return mk_bv_ext_rotate_right(args[0], args[1], result);
    case OP_BV2INT:
        SASSERT(num_args == 1);
        return mk_bv2int(args[0], result);
    case OP_INT2BV:
        SASSERT(num_args == 1);
        return mk_int2bv(m_util.get_bv_size(f->get_range()), args[0], result);
    case OP_BREDOR:
        SASSERT(num_args == 1);
        return mk_bv_redor(args[0], result);
    case OP_BREDAND:
        SASSERT(num_args == 1);
        return mk_bv_redand(args[0], result);
    case OP_BCOMP:
        SASSERT(num_args == 2);
        return mk_bv_comp(args[0], args[1], result);
    case OP_MKBV:
        return mk_mkbv(num_args, args, result);
    case OP_BIT2BOOL:
        SASSERT(num_args == 1);
        return mk_bit2bool(args[0], f->get_parameter(0).get_int(), result);
    case OP_BSMUL_NO_OVFL:
        return mk_bvsmul_no_overflow(num_args, args, result);
    case OP_BUMUL_NO_OVFL:
        return mk_bvumul_no_overflow(num_args, args, result);
    case OP_BSMUL_NO_UDFL:
        return mk_bvsmul_no_underflow(num_args, args, result);
    default:
        return BR_FAILED;
    }
}

br_status bv_rewriter::mk_ule(expr * a, expr * b, expr_ref & result) {
    return mk_leq_core(false, a, b, result);
}

br_status bv_rewriter::mk_uge(expr * a, expr * b, expr_ref & result) {
    br_status st = mk_ule(b, a, result);
    if (st != BR_FAILED)
        return st;
    result = m_util.mk_ule(b, a);
    return BR_DONE;
}

br_status bv_rewriter::mk_ult(expr * a, expr * b, expr_ref & result) {
    result = m().mk_not(m_util.mk_ule(b, a));
    return BR_REWRITE2;
}

br_status bv_rewriter::mk_sle(expr * a, expr * b, expr_ref & result) {
    return mk_leq_core(true, a, b, result);
}

br_status bv_rewriter::mk_sge(expr * a, expr * b, expr_ref & result) {
    br_status st = mk_sle(b, a, result);
    if (st != BR_FAILED)
        return st;
    result = m_util.mk_sle(b, a);
    return BR_DONE;
}

br_status bv_rewriter::mk_slt(expr * a, expr * b, expr_ref & result) {
    result = m().mk_not(m_util.mk_sle(b, a));
    return BR_REWRITE2;
}

// short-circuited concat
expr * bv_rewriter::concat(unsigned num_args, expr * const * args) {
    SASSERT(num_args);
    switch (num_args) {
        case 0: return m_util.mk_concat(num_args, args);
        case 1: return args[0];
        default: return m_util.mk_concat(num_args, args);
    }
}

// finds a commonality in sums, e.g.  2 + x + y and 5 + x + y
bool bv_rewriter::are_eq_upto_num(expr * _a, expr * _b,
        expr_ref& common,
        numeral& a0_val, numeral& b0_val) {
    const bool aadd = m_util.is_bv_add(_a);
    const bool badd = m_util.is_bv_add(_b);
    const bool has_num_a = aadd && to_app(_a)->get_num_args() && is_numeral(to_app(_a)->get_arg(0));
    const bool has_num_b = badd && to_app(_b)->get_num_args() && is_numeral(to_app(_b)->get_arg(0));
    a0_val = numeral::zero();
    b0_val = numeral::zero();
    if (!aadd && !badd) {
        if (_a == _b) {
            common = _a;
            return true;
        } else {
            return false;
        }
    }
    if (!aadd && badd) {
        if (to_app(_a)->get_num_args() != 2 || !has_num_a || to_app(_a)->get_arg(0) != _b)
            return false;
        common = _b;
        return true;
    }
    if (aadd && !badd) {
        if (to_app(_b)->get_num_args() != 2 || !has_num_b || to_app(_b)->get_arg(0) != _a)
            return false;
        common = _a;
        return true;
    }
    SASSERT(aadd && badd);
    app * const a = to_app(_a);
    app * const b = to_app(_b);
    const unsigned numa = a->get_num_args();
    const unsigned numb = b->get_num_args();
    if (!numa || !numb) return false;
    if ((numa - (has_num_a ? 1 : 0)) != (numb - (has_num_b ? 1 : 0))) return false;
    unsigned ai = has_num_a ? 1 : 0;
    unsigned bi = has_num_b ? 1 : 0;
    while (ai < numa) {
        if (a->get_arg(ai) != b->get_arg(bi)) return false;
        ++ai;
        ++bi;
    }
    a0_val = numeral::zero();
    b0_val = numeral::zero();
    const unsigned sz = m_util.get_bv_size(a);
    unsigned a0_sz(sz), b0_sz(sz);
    if (has_num_a) is_numeral(a->get_arg(0), a0_val, a0_sz);
    if (has_num_b) is_numeral(b->get_arg(0), b0_val, b0_sz);
    SASSERT(a0_sz == m_util.get_bv_size(a) && b0_sz == m_util.get_bv_size(a));
    if (has_num_a && numa > 2) {
        common = m().mk_app(m_util.get_fid(),  add_decl_kind(), numa - 1, a->get_args() + 1);
    }
    else {
        common = has_num_a ? a->get_arg(1) : a;
    }
    return true;
}

// simplifies expressions as (bvuleq (X + c1) (X + c2)) for some common expression X and numerals c1, c2
br_status bv_rewriter::rw_leq_overflow(bool is_signed, expr * a, expr * b, expr_ref & result) {
    if (is_signed) return BR_FAILED;
    expr_ref common(m());
    numeral a0_val, b0_val;
    if (!are_eq_upto_num(a, b, common, a0_val, b0_val)) return BR_FAILED;
    SASSERT(a0_val.is_nonneg() && b0_val.is_nonneg());
    const unsigned sz = m_util.get_bv_size(a);
    if (a0_val == b0_val) {
        result = m().mk_true();
        return BR_DONE;
    }
    if (a0_val < b0_val) {
        result = m_util.mk_ule(m_util.mk_numeral(b0_val - a0_val, sz), b);
        return BR_REWRITE2;
    }
    SASSERT(a0_val > b0_val);
    SASSERT(!a0_val.is_zero());
    const numeral lower = rational::power_of_two(sz) - a0_val;
    const numeral upper = rational::power_of_two(sz) - b0_val - numeral::one();
    if (lower == upper) {
        result = m().mk_eq(common, mk_numeral(lower, sz));
    }
    else if (b0_val.is_zero()) {
        result = m_util.mk_ule(mk_numeral(lower, sz), common);
    }
    else {
        SASSERT(lower.is_pos());
        result = m().mk_and(m_util.mk_ule(mk_numeral(lower, sz), common),
                            m_util.mk_ule(common, mk_numeral(upper, sz)));
    }
    return BR_REWRITE2;
}

// simplification for leq comparison between two concatenations
br_status bv_rewriter::rw_leq_concats(bool is_signed, expr * _a, expr * _b, expr_ref & result) {
    if (!m_util.is_concat(_a) || !m_util.is_concat(_b))
        return BR_FAILED;
    const app * const a = to_app(_a);
    const app * const b = to_app(_b);
    const unsigned numa = a->get_num_args();
    const unsigned numb = b->get_num_args();
    const unsigned num_min = std::min(numa, numb);

    if (numa && numb) { // first arg numeral
        numeral af, bf;
        unsigned af_sz, bf_sz;
        if (   is_numeral(a->get_arg(0), af, af_sz)
            && is_numeral(b->get_arg(0), bf, bf_sz) ) {
            const unsigned sz_min = std::min(af_sz, bf_sz);
            const numeral hi_af = m_util.norm(af_sz > sz_min ? div(af, rational::power_of_two(af_sz - sz_min)) : af,
                                              sz_min, is_signed);
            const numeral hi_bf = m_util.norm(bf_sz > sz_min ? div(bf, rational::power_of_two(bf_sz - sz_min)) : bf,
                                              sz_min, is_signed);
            if (hi_af != hi_bf) {
                result = hi_af < hi_bf ? m().mk_true() : m().mk_false();
                return BR_DONE;
            }
            expr_ref new_a(m());
            expr_ref new_b(m());
            if (af_sz > sz_min) {
                ptr_buffer<expr> new_args;
                new_args.push_back(mk_numeral(af, af_sz - sz_min));
                for (unsigned i = 1; i < numa; ++i) new_args.push_back(a->get_arg(i));
                new_a = concat(new_args.size(), new_args.c_ptr());
            } else {
                new_a = concat(numa - 1, a->get_args() + 1);
            }
            if (bf_sz > sz_min) {
                ptr_buffer<expr> new_args;
                new_args.push_back(mk_numeral(bf, bf_sz - sz_min));
                for (unsigned i = 1; i < numb; ++i) new_args.push_back(b->get_arg(i));
                new_b = concat(new_args.size(), new_args.c_ptr());
            } else {
                new_b = concat(numb - 1, b->get_args() + 1);
            }
            result = m_util.mk_ule(new_a, new_b);
            return BR_REWRITE2;
        }
    }

    { // common prefix
        unsigned common = 0;
        while (common < num_min && m().are_equal(a->get_arg(common), b->get_arg(common))) ++common;
        SASSERT((common == numa) == (common == numb));
        if (common == numa) {
            SASSERT(0); // shouldn't get here as both sides are equal
            result = m().mk_true();
            return BR_DONE;
        }
        if (common > 0) {
            result = m_util.mk_ule(concat(numa - common, a->get_args() + common),
                                   concat(numb - common, b->get_args() + common));
            return BR_REWRITE2;
        }
    }

    { // common postfix
        unsigned new_numa = a->get_num_args();
        unsigned new_numb = b->get_num_args();
        while (new_numa && new_numb) {
            expr * const last_a = a->get_arg(new_numa - 1);
            expr * const last_b = b->get_arg(new_numb - 1);
            if (!m().are_equal(last_a, last_b)) break;
            new_numa--;
            new_numb--;
        }
        if (new_numa == 0) {
            SASSERT(0); // shouldn't get here as both sides are equal
            result = m().mk_true();
            return BR_DONE;
        }
        if (new_numa != numa) {
            result = is_signed ? m_util.mk_sle(concat(new_numa, a->get_args()), concat(new_numb, b->get_args()))
                               : m_util.mk_ule(concat(new_numa, a->get_args()), concat(new_numb, b->get_args()));
            return BR_REWRITE2;
        }
    }

    return BR_FAILED;
}

br_status bv_rewriter::mk_leq_core(bool is_signed, expr * a, expr * b, expr_ref & result) {

    numeral r1, r2, r3;
    unsigned sz;
    bool is_num1     = is_numeral(a, r1, sz);
    bool is_num2     = is_numeral(b, r2, sz);

    if (a == b) {
        result = m().mk_true();
        return BR_DONE;
    }

    if (is_num1)
        r1 = m_util.norm(r1, sz, is_signed);
    if (is_num2)
        r2 = m_util.norm(r2, sz, is_signed);

    if (is_num1 && is_num2) {
        result = m().mk_bool_val(r1 <= r2);
        return BR_DONE;
    }

    numeral lower, upper;

    if (is_num1 || is_num2) {
        if (is_signed) {
            lower = - rational::power_of_two(sz - 1);
            upper =   rational::power_of_two(sz - 1) - numeral(1);
        }
        else {
            lower = numeral(0);
            upper = rational::power_of_two(sz) - numeral(1);
        }
    }

    if (is_num2) {
        if (r2 == lower) {
            result = m().mk_eq(a, b);
            return BR_REWRITE1;
        }
        if (r2 == upper) {
            result = m().mk_true();
            return BR_DONE;
        }
    }

    if (is_num1) {
        // 0 <= b is true
        if (r1 == lower) {
            result = m().mk_true();
            return BR_DONE;
        }

        // 2^n-1 <= b is a = b
        if (r1 == upper) {
            result = m().mk_eq(a, b);
            return BR_REWRITE1;
        }
    }

    expr* a1, *a2, *a3, *a4, *a5, *a6;
    // (bvsle (- x (srem x c1)) c2) -> (bvsle x (+ c1 c2 - 1))
    // (bvsle (+ x (* -1 (srem_i x c1))) c2)
    // pre: (and (> c1 0) (> c2 0) (= c2 % c1 0) (<= (+ c1 c2 -1) max_int))
    if (is_signed && is_num2 && 
        m_util.is_bv_add(a, a1, a2) &&
        m_util.is_bv_mul(a2, a3, a4) && is_numeral(a3, r1, sz) &&
        m_util.norm(r1, sz, is_signed).is_minus_one() &&
        m_util.is_bv_sremi(a4, a5, a6) && is_numeral(a6, r1, sz) &&
        (r1 = m_util.norm(r1, sz, is_signed), r1.is_pos()) &&
        r2.is_pos() &&
        (a1 == a5) && 
        (r2 % r1).is_zero() && r1 + r2 - rational::one() < rational::power_of_two(sz-1)) {
        result = m_util.mk_sle(a1, m_util.mk_numeral(r1 + r2 - rational::one(), sz));
        return BR_REWRITE2;
    }

    if (m_le_extra) {
        const br_status cst = rw_leq_concats(is_signed, a, b, result);
        if (cst != BR_FAILED) {
            TRACE("le_extra", tout << (is_signed ? "bv_sle\n" : "bv_ule\n")
                      << mk_ismt2_pp(a, m(), 2) <<  "\n" << mk_ismt2_pp(b, m(), 2) <<  "\n--->\n"<< mk_ismt2_pp(result, m(), 2) << "\n";);
            return cst;
        }
    }

    if (m_le_extra) {
        const br_status cst = rw_leq_overflow(is_signed, a, b, result);
        if (cst != BR_FAILED) {
            TRACE("le_extra", tout << (is_signed ? "bv_sle\n" : "bv_ule\n")
                      << mk_ismt2_pp(a, m(), 2) <<  "\n" << mk_ismt2_pp(b, m(), 2) <<  "\n--->\n"<< mk_ismt2_pp(result, m(), 2) << "\n";);
            return cst;
        }
    }

#if 0
    if (!is_signed && m_util.is_concat(b) && to_app(b)->get_num_args() == 2 && m_util.is_zero(to_app(b)->get_arg(0))) {
        //
        // a <=_u (concat 0 c) --->  a[h:l] = 0 && a[l-1:0] <=_u c
        //
        expr * b_1 = to_app(b)->get_arg(0);
        expr * b_2 = to_app(b)->get_arg(1);
        unsigned sz1 = get_bv_size(b_1);
        unsigned sz2 = get_bv_size(b_2);
        result = m().mk_and(m().mk_eq(m_mk_extract(sz2+sz1-1, sz2, a), b_1),
                            m_util.mk_ule(m_mk_extract(sz2-1, 0, a), b_2));
        return BR_REWRITE3;
    }
#else
    if (!is_signed) {
        // Extended version of the rule above using is_zero_bit.
        // It also catches examples atoms such as:
        //
        // a <=_u #x000f
        //
        unsigned bv_sz = m_util.get_bv_size(b);
        unsigned i     = bv_sz;
        unsigned first_non_zero = UINT_MAX;
        while (i > 0) {
            --i;
            if (!is_zero_bit(b, i)) {
                first_non_zero = i;
                break;
            }
        }

        if (first_non_zero == UINT_MAX) {
            // all bits are zero
            result = m().mk_eq(a, m_util.mk_numeral(numeral(0), bv_sz));
            return BR_REWRITE1;
        }
        else if (first_non_zero < bv_sz - 1) {
            result = m().mk_and(m().mk_eq(m_mk_extract(bv_sz - 1, first_non_zero + 1, a), m_util.mk_numeral(numeral(0), bv_sz - first_non_zero - 1)),
                                m_util.mk_ule(m_mk_extract(first_non_zero, 0, a), m_mk_extract(first_non_zero, 0, b)));
            return BR_REWRITE3;
        }

    }
#endif


    // Investigate if we need:
    //
    // k <=_s (concat 0 a) <=> (k[u:l] = 0 && k[l-1:0] <=_u a) || k[u:u] = bv1
    //
    // (concat 0 a) <=_s k <=> k[u:u] = bv0 && (k[u:l] != 0 || a <=_u k[l-1:0])
    //
    // (concat 0 a) <=_u k <=> k[u:l] != 0 || a <=_u k[l-1:0]
    //
    return BR_FAILED;
}

// attempt to chop off bits that are above the position high for  bv_mul and bv_add,
// returns how many bits were chopped off
// e.g.  (bvadd(concat #b11 p) #x1)) with high=1, returns 2 and  sets result = p + #b01
// the sz of results is the sz of arg minus the return value
unsigned bv_rewriter::propagate_extract(unsigned high, expr * arg, expr_ref & result) {
    if (!m_util.is_bv_add(arg) && !m_util.is_bv_mul(arg))
        return 0;
    const unsigned sz = m_util.get_bv_size(arg);
    const unsigned to_remove = high + 1 < sz ? sz - high - 1 : 0;
    if (to_remove == 0)
        return 0; // high goes to the top, nothing to do
    const app * const a = to_app(arg);
    const unsigned num = a->get_num_args();
    bool all_numerals = true;
    unsigned removable = to_remove;
    numeral val;
    unsigned curr_first_sz = -1;
    // calculate how much can be removed
    for (unsigned i = 0; i < num; i++) {
        expr * const curr = a->get_arg(i);
        const bool curr_is_conc = m_util.is_concat(curr);
        if (curr_is_conc && to_app(curr)->get_num_args() == 0) continue;
        expr * const curr_first = curr_is_conc ? to_app(curr)->get_arg(0) : curr;
        if (!all_numerals) {
            if (removable != m_util.get_bv_size(curr_first))
                return 0;
            continue;
        }
        if (is_numeral(curr_first, val, curr_first_sz)) {
            removable = std::min(removable, curr_first_sz);
        } else {
            all_numerals = false;
            curr_first_sz = m_util.get_bv_size(curr_first);
            if (curr_first_sz > removable) return 0;
            removable = curr_first_sz;
        }
        if (removable == 0) return 0;
    }
    // perform removal
    SASSERT(removable <= to_remove);
    ptr_buffer<expr> new_args;
    ptr_buffer<expr> new_concat_args;
    for (unsigned i = 0; i < num; i++) {
        expr * const curr = a->get_arg(i);
        const bool curr_is_conc = m_util.is_concat(curr);
        if (curr_is_conc && to_app(curr)->get_num_args() == 0) continue;
        expr * const curr_first = curr_is_conc ? to_app(curr)->get_arg(0) : curr;
        expr * new_first = nullptr;
        if (is_numeral(curr_first, val, curr_first_sz)) {
            SASSERT(curr_first_sz >= removable);
            const unsigned new_num_sz = curr_first_sz - removable;
            new_first = new_num_sz ? mk_numeral(val, new_num_sz) : nullptr;
        }
        expr * new_arg = nullptr;
        if (curr_is_conc) {
            const unsigned conc_num = to_app(curr)->get_num_args();
            if (new_first) {
                new_concat_args.reset();
                new_concat_args.push_back(new_first);
                for (unsigned j = 1; j < conc_num; ++j)
                    new_concat_args.push_back(to_app(curr)->get_arg(j));
                new_arg = m_util.mk_concat(new_concat_args.size(), new_concat_args.c_ptr());
            } else {
                // remove first element of concat
                expr * const * const old_conc_args = to_app(curr)->get_args();
                switch (conc_num) {
                    case 0: UNREACHABLE(); break;
                    case 1: new_arg = nullptr; break;
                    case 2: new_arg = to_app(curr)->get_arg(1); break;
                    default: new_arg = m_util.mk_concat(conc_num - 1, old_conc_args + 1);
                }
            }
        } else {
            new_arg = new_first;
        }
        if (new_arg) new_args.push_back(new_arg);
    }
    result = m().mk_app(get_fid(), a->get_decl()->get_decl_kind(), new_args.size(), new_args.c_ptr());
    SASSERT(m_util.is_bv(result));
    return removable;
}

br_status bv_rewriter::mk_extract(unsigned high, unsigned low, expr * arg, expr_ref & result) {
    unsigned sz = get_bv_size(arg);
    SASSERT(sz > 0);

    if (low == 0 && high == sz - 1) {
        result = arg;
        return BR_DONE;
    }

    numeral v;
    if (is_numeral(arg, v, sz)) {
        sz = high - low + 1;
        if (v.is_neg())
            mod(v, rational::power_of_two(sz), v);
        if (v.is_uint64()) {
            uint64_t u  = v.get_uint64();
            uint64_t e  = shift_right(u, low) & (shift_left(1ull, sz) - 1ull);
            result    = mk_numeral(numeral(e, numeral::ui64()), sz);
            return BR_DONE;
        }
        div(v, rational::power_of_two(low), v);
        result = mk_numeral(v, sz);
        return BR_DONE;
    }

    // (extract[high:low] (extract[high2:low2] x)) == (extract[high+low2 : low+low2] x)
    if (m_util.is_extract(arg)) {
        unsigned low2 = m_util.get_extract_low(arg);
        result = m_mk_extract(high + low2, low + low2, to_app(arg)->get_arg(0));
        return BR_DONE;
    }

    // (extract (concat ....)) --> (concat (extract ...) ... (extract ...) )
    if (m_util.is_concat(arg)) {
        unsigned num  = to_app(arg)->get_num_args();
        unsigned idx  = sz;
        for (unsigned i = 0; i < num; i++) {
            expr * curr      = to_app(arg)->get_arg(i);
            unsigned curr_sz = get_bv_size(curr);
            idx -= curr_sz;
            if (idx > high)
                continue;
            // found first argument
            if (idx <= low) {
                // result is a fragment of this argument
                if (low == idx && high - idx == curr_sz - 1) {
                    result = curr;
                    return BR_DONE;
                }
                else {
                    result = m_mk_extract(high - idx, low - idx, curr);
                    return BR_REWRITE1;
                }
            }
            else {
                // look for remaining arguments
                ptr_buffer<expr> new_args;
                bool used_extract = false;
                if (high - idx == curr_sz - 1) {
                    new_args.push_back(curr);
                }
                else {
                    used_extract = true;
                    new_args.push_back(m_mk_extract(high - idx, 0, curr));
                }
                for (unsigned j = i + 1; j < num; j++) {
                    curr = to_app(arg)->get_arg(j);
                    unsigned curr_sz = get_bv_size(curr);
                    idx -= curr_sz;
                    if (idx > low) {
                        new_args.push_back(curr);
                        continue;
                    }
                    if (idx == low) {
                        new_args.push_back(curr);
                        result = m_util.mk_concat(new_args.size(), new_args.c_ptr());
                        return used_extract ? BR_REWRITE2 : BR_DONE;
                    }
                    new_args.push_back(m_mk_extract(curr_sz - 1, low - idx, curr));
                    result = m_util.mk_concat(new_args.size(), new_args.c_ptr());
                    return BR_REWRITE2;
                }
                UNREACHABLE();
            }
        }
        UNREACHABLE();
    }

    if (m_util.is_bv_not(arg) ||
        m_util.is_bv_or(arg)  ||
        m_util.is_bv_xor(arg) ||
        (low == 0 && (m_util.is_bv_add(arg) ||
                      m_util.is_bv_mul(arg)))) {
        ptr_buffer<expr> new_args;
        unsigned num = to_app(arg)->get_num_args();
        for (unsigned i = 0; i < num; i++) {
            expr * curr = to_app(arg)->get_arg(i);
            new_args.push_back(m_mk_extract(high, low, curr));
        }
        result = m().mk_app(get_fid(), to_app(arg)->get_decl()->get_decl_kind(), new_args.size(), new_args.c_ptr());
        return BR_REWRITE2;
    }

    if (m_extract_prop && (high >= low)) {
        expr_ref ep_res(m());
        const unsigned ep_rm = propagate_extract(high, arg, ep_res);
        if (ep_rm != 0) {
            result = m_mk_extract(high, low, ep_res);
            TRACE("extract_prop", tout << mk_ismt2_pp(arg, m()) << "\n[" << high <<"," << low << "]\n" << ep_rm << "---->\n"
                                       << mk_ismt2_pp(result.get(), m()) << "\n";);
            return BR_REWRITE2;
        }
    }

    // issue #2359 led to relaxing condition for propagating extract over ite.
    // It is propagted inwards only in the case that it leads to at most one
    // branch of ite to be expanded or if one of the expanded ite branches have a single 
    // reference count.
    expr* c = nullptr, *t = nullptr, *e = nullptr;
    if (m().is_ite(arg, c, t, e) &&
        (t->get_ref_count() == 1 || e->get_ref_count() == 1 || !m().is_ite(t) || !m().is_ite(e))) {
        result = m().mk_ite(c, m_mk_extract(high, low, t), m_mk_extract(high, low, e));
        return BR_REWRITE2;
    }

    return BR_FAILED;
}

br_status bv_rewriter::mk_bv_shl(expr * arg1, expr * arg2, expr_ref & result) {
    numeral r1, r2;
    unsigned bv_size = get_bv_size(arg1);
    unsigned sz;

    if (is_numeral(arg2, r2, sz)) {
        if (r2.is_zero()) {
            // x << 0  ==  x
            result = arg1;
            return BR_DONE;
        }

        if (r2 >= numeral(bv_size)) {
            result = mk_numeral(0, bv_size);
            return BR_DONE;
        }

        if (is_numeral(arg1, r1, sz)) {
            if (bv_size <= 64) {
                SASSERT(r1.is_uint64() && r2.is_uint64());
                SASSERT(r2.get_uint64() < bv_size);

                uint64_t r = shift_left(r1.get_uint64(), r2.get_uint64());
                numeral rn(r, numeral::ui64());
                rn = m_util.norm(rn, bv_size);
                result   = mk_numeral(rn, bv_size);
                return BR_DONE;
            }


            SASSERT(r2 < numeral(bv_size));
            SASSERT(r2.is_unsigned());
            r1 = m_util.norm(r1 * rational::power_of_two(r2.get_unsigned()), bv_size);
            result = mk_numeral(r1, bv_size);
            return BR_DONE;
        }

        SASSERT(r2.is_pos());
        SASSERT(r2 < numeral(bv_size));
        // (bvshl x k) -> (concat (extract [n-1-k:0] x) bv0:k)
        unsigned k = r2.get_unsigned();
        expr * new_args[2] = { m_mk_extract(bv_size - k - 1, 0, arg1),
                               mk_numeral(0, k) };
        result = m_util.mk_concat(2, new_args);
        return BR_REWRITE2;
    }

    return BR_FAILED;
}

br_status bv_rewriter::mk_bv_lshr(expr * arg1, expr * arg2, expr_ref & result) {
    numeral r1, r2;
    unsigned bv_size = get_bv_size(arg1);
    unsigned sz;

    if (is_numeral(arg2, r2, sz)) {
        if (r2.is_zero()) {
            // x >> 0 == x
            result = arg1;
            return BR_DONE;
        }

        if (r2 >= numeral(bv_size)) {
            result = mk_numeral(0, bv_size);
            return BR_DONE;
        }

        if (is_numeral(arg1, r1, sz)) {
            if (bv_size <= 64) {
                SASSERT(r1.is_uint64());
                SASSERT(r2.is_uint64());
                uint64_t r = shift_right(r1.get_uint64(), r2.get_uint64());
                numeral rn(r, numeral::ui64());
                rn = m_util.norm(rn, bv_size);
                result = mk_numeral(rn, bv_size);
                return BR_DONE;
            }

            SASSERT(r2.is_unsigned());
            unsigned sh = r2.get_unsigned();
            div(r1, rational::power_of_two(sh), r1);
            result = mk_numeral(r1, bv_size);
            return BR_DONE;
        }

        SASSERT(r2.is_pos());
        SASSERT(r2 < numeral(bv_size));
        // (bvlshr x k) -> (concat bv0:k (extract [n-1:k] x))
        SASSERT(r2.is_unsigned());
        unsigned k = r2.get_unsigned();
        expr * new_args[2] = { mk_numeral(0, k),
                               m_mk_extract(bv_size - 1, k, arg1) };
        result = m_util.mk_concat(2, new_args);
        return BR_REWRITE2;
    }

    return BR_FAILED;
}

br_status bv_rewriter::mk_bv_ashr(expr * arg1, expr * arg2, expr_ref & result) {
    numeral r1, r2;
    unsigned bv_size = get_bv_size(arg1);
    SASSERT(bv_size > 0);
    bool is_num2 = is_numeral(arg2, r2, bv_size);

    if (is_num2 && r2.is_zero()) {
        result = arg1;
        return BR_DONE;
    }

    bool is_num1 = is_numeral(arg1, r1, bv_size);

    if (bv_size <= 64 && is_num1 && is_num2) {
        uint64_t n1      = r1.get_uint64();
        uint64_t n2_orig = r2.get_uint64();
        uint64_t n2      = n2_orig % bv_size;
        SASSERT(n2 < bv_size);
        uint64_t r       = shift_right(n1, n2);
        bool   sign    = (n1 & shift_left(1ull, bv_size - 1ull)) != 0;
        if (n2_orig > n2) {
            if (sign) {
                r = shift_left(1ull, bv_size) - 1ull;
            }
            else {
                r = 0;
            }
        }
        else if (sign) {
            uint64_t allone = shift_left(1ull, bv_size) - 1ull;
            uint64_t mask   = ~(shift_left(1ull, bv_size - n2) - 1ull);
            mask &= allone;
            r |= mask;
        }
        result = mk_numeral(numeral(r, numeral::ui64()), bv_size);
        return BR_DONE;
    }

    if (is_num1 && is_num2 && numeral(bv_size) <= r2) {
        if (m_util.has_sign_bit(r1, bv_size))
            result = mk_numeral(rational::power_of_two(bv_size) - numeral(1), bv_size);
        else
            result = mk_numeral(0, bv_size);
        return BR_DONE;
    }

    if (is_num1 && is_num2) {
        SASSERT(r2 < numeral(bv_size));
        bool   sign = m_util.has_sign_bit(r1, bv_size);
        div(r1, rational::power_of_two(r2.get_unsigned()), r1);
        if (sign) {
            // pad ones.
            numeral p(1);
            for (unsigned i = 0; i < bv_size; ++i) {
                if (r1 < p) {
                    r1 += p;
                }
                p *= numeral(2);
            }
        }
        result = mk_numeral(r1, bv_size);
        return BR_DONE;
    }

    // (bvashr (bvashr x r1) r2) --> (bvashr x r1+r2)
    if (is_num2 && m_util.is_bv_ashr(arg1) && is_numeral(to_app(arg1)->get_arg(1), r1, bv_size)) {
        r1 += r2;
        if (r1 > numeral(bv_size))
            r1 = numeral(bv_size);
        result = m().mk_app(get_fid(), OP_BASHR,
                            to_app(arg1)->get_arg(0),
                            mk_numeral(r1, bv_size));
        return BR_REWRITE1; // not really needed at this time.
    }

#if 0
    // (bvashr x k) --> (concat extract[sz-1:sz-1](x) ... extract[sz-1:sz-1](x) extract[sz-1:k](x))
    if (is_num2) {
        ptr_buffer<expr> new_args;
        if (r2 > numeral(bv_size))
            r2 = numeral(bv_size);
        SASSERT(r2 <= numeral(bv_size));
        unsigned k  = r2.get_unsigned();
        expr * sign = m_mk_extract(bv_size-1, bv_size-1, arg1);
        for (unsigned i = 0; i < k; i++)
            new_args.push_back(sign);
        if (k != bv_size)
            new_args.push_back(m_mk_extract(bv_size-1, k, arg1));
        result = m_util.mk_concat(new_args.size(), new_args.c_ptr());
        return BR_REWRITE2;
    }
#endif

    return BR_FAILED;
}

br_status bv_rewriter::mk_bv_sdiv_core(expr * arg1, expr * arg2, bool hi_div0, expr_ref & result) {
    numeral r1, r2;
    unsigned bv_size;

    if (is_numeral(arg2, r2, bv_size)) {
        r2 = m_util.norm(r2, bv_size, true);
        if (r2.is_zero()) {
            if (!hi_div0) {
                result = m().mk_app(get_fid(), OP_BSDIV0, arg1);
                return BR_REWRITE1;
            }
            else {
                // The "hardware interpretation" for (bvsdiv x 0) is (ite (bvslt x #x0000) #x0001 #xffff)
                result = m().mk_ite(m().mk_app(get_fid(), OP_SLT, arg1, mk_numeral(0, bv_size)),
                                    mk_numeral(1, bv_size),
                                    mk_numeral(rational::power_of_two(bv_size) - numeral(1), bv_size));
                return BR_REWRITE2;
            }
        }

        if (r2.is_one()) {
            result = arg1;
            return BR_DONE;
        }

        if (!r2.is_zero() && is_numeral(arg1, r1, bv_size)) {
            r1 = m_util.norm(r1, bv_size, true);
            result = mk_numeral(machine_div(r1, r2), bv_size);
            return BR_DONE;
        }

        result = m().mk_app(get_fid(), OP_BSDIV_I, arg1, arg2);
        return BR_DONE;
    }

    if (hi_div0) {
        result = m().mk_app(get_fid(), OP_BSDIV_I, arg1, arg2);
        return BR_DONE;
    }

    bv_size = get_bv_size(arg2);
    result = m().mk_ite(m().mk_eq(arg2, mk_numeral(0, bv_size)),
                        m().mk_app(get_fid(), OP_BSDIV0, arg1),
                        m().mk_app(get_fid(), OP_BSDIV_I, arg1, arg2));
    return BR_REWRITE2;
}

br_status bv_rewriter::mk_bv_udiv_core(expr * arg1, expr * arg2, bool hi_div0, expr_ref & result) {
    numeral r1, r2;
    unsigned bv_size;

    TRACE("bv_udiv", tout << "hi_div0: " << hi_div0 << "\n";);

    TRACE("udiv2mul", tout << mk_ismt2_pp(arg2, m()) << " udiv2mul: " << m_udiv2mul << "\n";);

    if (is_numeral(arg2, r2, bv_size)) {
        r2 = m_util.norm(r2, bv_size);
        if (r2.is_zero()) {
            if (!hi_div0) {
                result = m().mk_app(get_fid(), OP_BUDIV0, arg1);
                return BR_REWRITE1;
            }
            else {
                // The "hardware interpretation" for (bvudiv x 0) is #xffff
                result = mk_numeral(rational::power_of_two(bv_size) - numeral(1), bv_size);
                return BR_DONE;

            }
        }

        if (r2.is_one()) {
            result = arg1;
            return BR_DONE;
        }

        if (!r2.is_zero() && is_numeral(arg1, r1, bv_size)) {
            r1 = m_util.norm(r1, bv_size);
            result = mk_numeral(machine_div(r1, r2), bv_size);
            return BR_DONE;
        }

        unsigned shift;
        if (r2.is_power_of_two(shift)) {
            result = m().mk_app(get_fid(), OP_BLSHR, arg1, mk_numeral(shift, bv_size));
            return BR_REWRITE1;
        }

        if (m_udiv2mul) {
            TRACE("udiv2mul", tout << "using udiv2mul\n";);
            numeral inv_r2;
            if (m_util.mult_inverse(r2, bv_size, inv_r2)) {
                result = m().mk_app(get_fid(), OP_BMUL, mk_numeral(inv_r2, bv_size), arg1);
                return BR_REWRITE1;
            }
        }

        result = m().mk_app(get_fid(), OP_BUDIV_I, arg1, arg2);
        return BR_DONE;
    }

    if (hi_div0) {
        result = m().mk_app(get_fid(), OP_BUDIV_I, arg1, arg2);
        return BR_DONE;
    }

    bv_size = get_bv_size(arg2);
    result = m().mk_ite(m().mk_eq(arg2, mk_numeral(0, bv_size)),
                        m().mk_app(get_fid(), OP_BUDIV0, arg1),
                        m().mk_app(get_fid(), OP_BUDIV_I, arg1, arg2));

    TRACE("bv_udiv", tout << mk_ismt2_pp(arg1, m()) << "\n" << mk_ismt2_pp(arg2, m()) << "\n---->\n" << mk_ismt2_pp(result, m()) << "\n";);
    return BR_REWRITE2;
}

br_status bv_rewriter::mk_bv_srem_core(expr * arg1, expr * arg2, bool hi_div0, expr_ref & result) {
    numeral r1, r2;
    unsigned bv_size;

    if (is_numeral(arg2, r2, bv_size)) {
        r2 = m_util.norm(r2, bv_size, true);
        if (r2.is_zero()) {
            if (!hi_div0) {
                result = m().mk_app(get_fid(), OP_BSREM0, arg1);
                return BR_REWRITE1;
            }
            else {
                // The "hardware interpretation" for (bvsrem x 0) is x
                result = arg1;
                return BR_DONE;
            }
        }

        if (r2.is_one()) {
            result = mk_numeral(0, bv_size);
            return BR_DONE;
        }

        if (!r2.is_zero() && is_numeral(arg1, r1, bv_size)) {
            r1 = m_util.norm(r1, bv_size, true);
            result = mk_numeral(r1 % r2, bv_size);
            return BR_DONE;
        }

        result = m().mk_app(get_fid(), OP_BSREM_I, arg1, arg2);
        return BR_DONE;
    }

    if (hi_div0) {
        result = m().mk_app(get_fid(), OP_BSREM_I, arg1, arg2);
        return BR_DONE;
    }

    bv_size = get_bv_size(arg2);
    result = m().mk_ite(m().mk_eq(arg2, mk_numeral(0, bv_size)),
                        m().mk_app(get_fid(), OP_BSREM0, arg1),
                        m().mk_app(get_fid(), OP_BSREM_I, arg1, arg2));
    return BR_REWRITE2;
}

bool bv_rewriter::is_minus_one_core(expr * arg) const {
    numeral r;
    unsigned bv_size;
    if (is_numeral(arg, r, bv_size)) {
        return r == (rational::power_of_two(bv_size) - numeral(1));
    }
    return false;
}

bool bv_rewriter::is_negatable(expr * arg, expr_ref& x) {
    numeral r;
    unsigned bv_size;
    if (is_numeral(arg, r, bv_size)) {
        r = bitwise_not(bv_size, r);
        x = mk_numeral(r, bv_size);
        return true;
    }
    if (m_util.is_bv_not(arg)) {
        SASSERT(to_app(arg)->get_num_args() == 1);
        x =  to_app(arg)->get_arg(0);
        return true;
    }
    return false;
}

bool bv_rewriter::is_x_minus_one(expr * arg, expr * & x) {
    if (is_add(arg) && to_app(arg)->get_num_args() == 2) {
        if (is_minus_one_core(to_app(arg)->get_arg(0))) {
            x = to_app(arg)->get_arg(1);
            return true;
        }
        if (is_minus_one_core(to_app(arg)->get_arg(1))) {
            x = to_app(arg)->get_arg(0);
            return true;
        }
    }
    return false;
}

br_status bv_rewriter::mk_bv_urem_core(expr * arg1, expr * arg2, bool hi_div0, expr_ref & result) {
    numeral r1, r2;
    unsigned bv_size;
    bool is_num1 = is_numeral(arg1, r1, bv_size);

    if (is_numeral(arg2, r2, bv_size)) {
        r2 = m_util.norm(r2, bv_size);
        if (r2.is_zero()) {
            if (!hi_div0) {
                result = m().mk_app(get_fid(), OP_BUREM0, arg1);
                return BR_REWRITE1;
            }
            else {
                // The "hardware interpretation" for (bvurem x 0) is x
                result = arg1;
                return BR_DONE;
            }
        }

        if (r2.is_one()) {
            result = mk_numeral(0, bv_size);
            return BR_DONE;
        }

        if (!r2.is_zero() && is_num1) {
            r1 = m_util.norm(r1, bv_size);
            r1 %= r2;
            result = mk_numeral(r1, bv_size);
            return BR_DONE;
        }

        unsigned shift;
        if (r2.is_power_of_two(shift)) {
            expr * args[2] = {
                mk_numeral(0, bv_size - shift),
                m_mk_extract(shift-1, 0, arg1)
            };
            result = m_util.mk_concat(2, args);
            return BR_REWRITE2;
        }

        result = m().mk_app(get_fid(), OP_BUREM_I, arg1, arg2);
        return BR_DONE;
    }

    if (!hi_div0) {
        // urem(0, x) ==> ite(x = 0, urem0(x), 0)
        if (is_num1 && r1.is_zero()) {
            expr * zero = arg1;
            result = m().mk_ite(m().mk_eq(arg2, zero),
                                m().mk_app(get_fid(), OP_BUREM0, zero),
                                zero);
            return BR_REWRITE2;
        }

        // urem(x - 1, x) ==> ite(x = 0, urem0(x-1), x - 1) ==> ite(x = 0, urem0(-1), x - 1)
        expr * x;
        if (is_x_minus_one(arg1, x) && x == arg2) {
            bv_size = get_bv_size(arg1);
            expr * x_minus_1 = arg1;
            expr * minus_one = mk_numeral(rational::power_of_two(bv_size) - numeral(1), bv_size);
            result = m().mk_ite(m().mk_eq(x, mk_numeral(0, bv_size)),
                                m().mk_app(get_fid(), OP_BUREM0, minus_one),
                                x_minus_1);
            return BR_REWRITE2;
        }
    }
    else {
        // Remark: when HI_DIV0=true is used, (bvurem x 0) --> x
        if (is_num1 && r1.is_zero()) {
            // urem(0, x) --> 0
            expr * zero = arg1;
            result = zero;
            return BR_DONE;
        }

        // urem(x - 1, x) --> x - 1
        expr * x;
        if (is_x_minus_one(arg1, x) && x == arg2) {
            expr * x_minus_1 = arg1;
            result = x_minus_1;
            return BR_DONE;
        }
    }

    if (hi_div0) {
        result = m().mk_app(get_fid(), OP_BUREM_I, arg1, arg2);
        return BR_DONE;
    }

    bv_size = get_bv_size(arg2);
    result = m().mk_ite(m().mk_eq(arg2, mk_numeral(0, bv_size)),
                        m().mk_app(get_fid(), OP_BUREM0, arg1),
                        m().mk_app(get_fid(), OP_BUREM_I, arg1, arg2));
    return BR_REWRITE2;
}

br_status bv_rewriter::mk_bv_smod_core(expr * arg1, expr * arg2, bool hi_div0, expr_ref & result) {
    numeral r1, r2;
    unsigned bv_size;

    bool is_num1 = is_numeral(arg1, r1, bv_size);
    if (is_num1) {
        r1 = m_util.norm(r1, bv_size, true);
        if (r1.is_zero()) {
            result = m().mk_app(get_fid(), OP_BUREM, arg1, arg2);
            return BR_REWRITE1;
        }
    }

    if (is_numeral(arg2, r2, bv_size)) {
        r2 = m_util.norm(r2, bv_size, true);
        if (r2.is_zero()) {
            if (!hi_div0)
                result = m().mk_app(get_fid(), OP_BSMOD0, arg1);
            else
                result = arg1;
            return BR_DONE;
        }

        if (is_num1) {
            numeral abs_r1 = m_util.norm(abs(r1), bv_size);
            numeral abs_r2 = m_util.norm(abs(r2), bv_size);
            numeral u      = m_util.norm(abs_r1 % abs_r2, bv_size);
            numeral r;
            if (u.is_zero())
                r = u;
            else if (r1.is_pos() && r2.is_pos())
                r = u;
            else if (r1.is_neg() && r2.is_pos())
                r = m_util.norm(-u + r2, bv_size);
            else if (r1.is_pos() && r2.is_neg())
                r = m_util.norm(u + r2, bv_size);
            else
                r = m_util.norm(-u, bv_size);
            result = mk_numeral(r, bv_size);
            return BR_DONE;
        }

        if (r2.is_one()) {
            // (bvsmod x 1) -->  0
            result = mk_numeral(0, bv_size);
            return BR_REWRITE2;
        }
    }

    if (hi_div0) {
        result = m().mk_app(get_fid(), OP_BSMOD_I, arg1, arg2);
        return BR_DONE;
    }

    bv_size = get_bv_size(arg2);
    result = m().mk_ite(m().mk_eq(arg2, mk_numeral(0, bv_size)),
                        m().mk_app(get_fid(), OP_BSMOD0, arg1),
                        m().mk_app(get_fid(), OP_BSMOD_I, arg1, arg2));
    return BR_REWRITE2;
}

br_status bv_rewriter::mk_int2bv(unsigned bv_size, expr * arg, expr_ref & result) {
    numeral val;
    bool is_int;

    if (m_autil.is_numeral(arg, val, is_int)) {
        val = m_util.norm(val, bv_size);
        result = mk_numeral(val, bv_size);
        return BR_DONE;
    }

    // (int2bv (bv2int x)) --> x
    if (m_util.is_bv2int(arg) && bv_size == get_bv_size(to_app(arg)->get_arg(0))) {
        result = to_app(arg)->get_arg(0);
        return BR_DONE;
    }

    return BR_FAILED;
}

br_status bv_rewriter::mk_bv2int(expr * arg, expr_ref & result) {
    numeral v;
    unsigned sz;
    if (is_numeral(arg, v, sz)) {
        result = m_autil.mk_numeral(v, true);
        return BR_DONE;
    }
    if (m_util.is_concat(arg)) {
        if (to_app(arg)->get_num_args() == 0) {
            result = m_autil.mk_int(0);
            return BR_DONE;
        }
        expr_ref_vector args(m());        
        
        unsigned num_args = to_app(arg)->get_num_args();
        for (expr* x : *to_app(arg)) {
            args.push_back(m_util.mk_bv2int(x));
        }
        unsigned sz = get_bv_size(to_app(arg)->get_arg(num_args-1));
        for (unsigned i = num_args - 1; i > 0; ) {
            expr_ref tmp(m());
            --i;
            tmp = args[i].get();
            tmp = m_autil.mk_mul(m_autil.mk_numeral(power(numeral(2), sz), true), tmp);
            args[i] = std::move(tmp);
            sz += get_bv_size(to_app(arg)->get_arg(i));
        }
        result = m_autil.mk_add(args.size(), args.c_ptr());
        return BR_REWRITE2;
    }
    if (is_mul_no_overflow(arg)) {
        expr_ref_vector args(m());
        for (expr* x : *to_app(arg)) args.push_back(m_util.mk_bv2int(x));
        result = m_autil.mk_mul(args.size(), args.c_ptr());
        return BR_REWRITE2;
    }
    if (is_add_no_overflow(arg)) {
        expr_ref_vector args(m());
        for (expr* x : *to_app(arg)) args.push_back(m_util.mk_bv2int(x));
        result = m_autil.mk_add(args.size(), args.c_ptr());
        return BR_REWRITE2;
    }

    return BR_FAILED;
}


bool bv_rewriter::is_mul_no_overflow(expr* e) {
    if (!m_util.is_bv_mul(e)) return false;
    unsigned sz = get_bv_size(e);
    unsigned sum = 0;
    for (expr* x : *to_app(e)) sum += sz-num_leading_zero_bits(x);
    return sum < sz;
}

bool bv_rewriter::is_add_no_overflow(expr* e) {
    if (!is_add(e)) return false;
    for (expr* x : *to_app(e)) {
        if (0 == num_leading_zero_bits(x)) return false;
    }
    return true;
}

unsigned bv_rewriter::num_leading_zero_bits(expr* e) {
    numeral v;
    unsigned sz = get_bv_size(e);
    if (m_util.is_numeral(e, v)) {
        while (v.is_pos()) {
            SASSERT(sz > 0);
            --sz;
            v = div(v, numeral(2));
        }
        return sz;
    }
    else if (m_util.is_concat(e)) {
        app* a = to_app(e);
        unsigned sz1 = get_bv_size(a->get_arg(0));
        unsigned nb1 = num_leading_zero_bits(a->get_arg(0));
        if (sz1 == nb1) {
            nb1 += num_leading_zero_bits(a->get_arg(1));
        }
        return nb1;
    }
    return 0;
}




br_status bv_rewriter::mk_concat(unsigned num_args, expr * const * args, expr_ref & result) {
    expr_ref_buffer new_args(m());
    numeral v1;
    numeral v2;
    unsigned sz1, sz2;
    bool fused_numeral = false;
    bool expanded      = false;
    bool fused_extract = false;
    for (unsigned i = 0; i < num_args; i++) {
        expr * arg = args[i];
        expr * prev = nullptr;
        if (i > 0)
            prev = new_args.back();
        if (is_numeral(arg, v1, sz1) && prev != nullptr && is_numeral(prev, v2, sz2)) {
            v2  *= rational::power_of_two(sz1);
            v2  += v1;
            new_args.pop_back();
            new_args.push_back(mk_numeral(v2, sz1+sz2));
            fused_numeral = true;
        }
        else if (m_flat && m_util.is_concat(arg)) {
            unsigned num2 = to_app(arg)->get_num_args();
            for (unsigned j = 0; j < num2; j++) {
                new_args.push_back(to_app(arg)->get_arg(j));
            }
            expanded = true;
        }
        else if (m_util.is_extract(arg) &&
                 prev != nullptr &&
                 m_util.is_extract(prev) &&
                 to_app(arg)->get_arg(0) == to_app(prev)->get_arg(0) &&
                 m_util.get_extract_low(prev) == m_util.get_extract_high(arg) + 1) {
            // (concat (extract[h1,l1] a) (extract[h2,l2] a)) --> (extract[h1,l2] a)  if l1 == h2+1
            expr * new_arg = m_mk_extract(m_util.get_extract_high(prev),
                                               m_util.get_extract_low(arg),
                                               to_app(arg)->get_arg(0));
            new_args.pop_back();
            new_args.push_back(new_arg);
            fused_extract = true;
        }
        else {
            new_args.push_back(arg);
        }
    }
    if (!fused_numeral && !expanded && !fused_extract)
        return BR_FAILED;
    SASSERT(!new_args.empty());
    if (new_args.size() == 1) {
        result = new_args.back();
        return fused_extract ? BR_REWRITE1 : BR_DONE;
    }
    result = m_util.mk_concat(new_args.size(), new_args.c_ptr());
    if (fused_extract)
        return BR_REWRITE2;
    else if (expanded)
        return BR_REWRITE1;
    else
        return BR_DONE;
}



br_status bv_rewriter::mk_zero_extend(unsigned n, expr * arg, expr_ref & result) {
    if (n == 0) {
        result = arg;
        return BR_DONE;
    }
    else {
        expr * args[2] = { mk_numeral(0, n), arg };
        result = m_util.mk_concat(2, args);
        return BR_REWRITE1;
    }
}

br_status bv_rewriter::mk_sign_extend(unsigned n, expr * arg, expr_ref & result) {
    if (n == 0) {
        result = arg;
        return BR_DONE;
    }

    numeral r;
    unsigned bv_size;
    if (is_numeral(arg, r, bv_size)) {
        unsigned result_bv_size = bv_size + n;
        r = m_util.norm(r, bv_size, true);
        mod(r, rational::power_of_two(result_bv_size), r);
        result = mk_numeral(r, result_bv_size);
        return BR_DONE;
    }

    if (m_elim_sign_ext) {
        unsigned sz = get_bv_size(arg);
        expr * sign = m_mk_extract(sz-1, sz-1, arg);
        ptr_buffer<expr> args;
        for (unsigned i = 0; i < n; i++)
            args.push_back(sign);
        args.push_back(arg);
        result = m_util.mk_concat(args.size(), args.c_ptr());
        return BR_REWRITE2;
    }

    return BR_FAILED;
}

br_status bv_rewriter::mk_repeat(unsigned n, expr * arg, expr_ref & result) {
    if (n == 1) {
        result = arg;
        return BR_DONE;
    }
    ptr_buffer<expr> args;
    for (unsigned i = 0; i < n; i++)
        args.push_back(arg);
    result = m_util.mk_concat(args.size(), args.c_ptr());
    return BR_REWRITE1;
}

br_status bv_rewriter::mk_bv_or(unsigned num, expr * const * args, expr_ref & result) {
    SASSERT(num > 0);
    if (num == 1) {
        result = args[0];
        return BR_DONE;
    }
    unsigned sz    = get_bv_size(args[0]);
    bool flattened = false;
    ptr_buffer<expr> flat_args;
    if (m_flat) {
        for (unsigned i = 0; i < num; i++) {
            expr * arg = args[i];
            if (m_util.is_bv_or(arg)) {
                unsigned num2 = to_app(arg)->get_num_args();
                for (unsigned j = 0; j < num2; j++)
                    flat_args.push_back(to_app(arg)->get_arg(j));
            }
            else {
                flat_args.push_back(arg);
            }
        }
        if (flat_args.size() != num) {
            flattened = true;
            num  = flat_args.size();
            args = flat_args.c_ptr();
        }
    }

    ptr_buffer<expr> new_args;
    expr_fast_mark1  pos_args;
    expr_fast_mark2  neg_args;
    bool merged = false;
    unsigned num_coeffs = 0;
    numeral v1, v2;
    for (unsigned i = 0; i < num; i++) {
        expr * arg = args[i];
        if (is_numeral(arg, v2, sz)) {
            num_coeffs++;
            v1 = bitwise_or(v1, v2);
            continue;
        }

        if (m_util.is_bv_not(arg)) {
            expr * atom = to_app(arg)->get_arg(0);
            if (pos_args.is_marked(atom)) {
                result = mk_numeral(rational::power_of_two(sz) - numeral(1), sz);
                return BR_DONE;
            }
            else if (neg_args.is_marked(atom)) {
                merged = true;
                continue;
            }
            neg_args.mark(atom, true);
            new_args.push_back(arg);
        }
        else {
            if (pos_args.is_marked(arg)) {
                merged = true;
                continue;
            }
            else if (neg_args.is_marked(arg)) {
                result = mk_numeral(rational::power_of_two(sz) - numeral(1), sz);
                return BR_DONE;
            }
            pos_args.mark(arg, true);
            new_args.push_back(arg);
        }
    }

    if (v1 == rational::power_of_two(sz) - numeral(1)) {
        result = mk_numeral(v1, sz);
        return BR_DONE;
    }

    // Simplifications of the form:
    // (bvor (concat x #x00) (concat #x00 y)) --> (concat x y)
    if (new_args.size() == 2 &&
        num_coeffs == 0 &&
        m_util.is_concat(new_args[0]) &&
        m_util.is_concat(new_args[1])) {
        app * concat1 = to_app(new_args[0]);
        app * concat2 = to_app(new_args[1]);
        unsigned i = 0;
        for (i = 0; i < sz; i++)
            if (!is_zero_bit(concat1, i) && !is_zero_bit(concat2, i))
                break;
        if (i == sz) {
            // is target
            ptr_buffer<expr> non_zero_args;
            int j = sz;
            j--;
            while (j >= 0) {
                int high = j;
                while (j >= 0 && is_zero_bit(concat1, j))
                    --j;
                if (j != high)
                    non_zero_args.push_back(m_mk_extract(high, j+1, concat2));
                high = j;
                while (j >= 0 && is_zero_bit(concat2, j))
                    --j;
                if (j != high)
                    non_zero_args.push_back(m_mk_extract(high, j+1, concat1));
            }
            result = m_util.mk_concat(non_zero_args.size(), non_zero_args.c_ptr());
            return BR_REWRITE2;
        }
    }

    if (!v1.is_zero() && new_args.size() == 1) {
        v1 = m_util.norm(v1, sz);
#ifdef _TRACE
        numeral old_v1 = v1;
#endif
        // OR is a mask
        expr * t = new_args[0];
        numeral two(2);
        ptr_buffer<expr> exs;
        unsigned low = 0;
        unsigned i = 0;
        while (i < sz) {
            while (i < sz && mod(v1, two).is_one()) {
                i++;
                div(v1, two, v1);
            }
            if (i != low) {
                unsigned num_sz = i - low;
                exs.push_back(m_util.mk_numeral(rational::power_of_two(num_sz) - numeral(1), num_sz));
                low = i;
            }
            while (i < sz && mod(v1, two).is_zero()) {
                i++;
                div(v1, two, v1);
            }
            if (i != low) {
                exs.push_back(m_mk_extract(i-1, low, t));
                low = i;
            }
        }
        std::reverse(exs.begin(), exs.end());
        result = m_util.mk_concat(exs.size(), exs.c_ptr());
        TRACE("mask_bug",
              tout << "(assert (distinct (bvor (_ bv" << old_v1 << " " << sz << ")\n" << mk_ismt2_pp(t, m()) << ")\n";
              tout << mk_ismt2_pp(result, m()) << "))\n";);
        return BR_REWRITE2;
    }

    if (!flattened && !merged && (num_coeffs == 0 || (num_coeffs == 1 && !v1.is_zero())) && (!m_bv_sort_ac || is_sorted(num, args))) {
        return BR_FAILED;
    }

    if (!v1.is_zero()) {
        new_args.push_back(mk_numeral(v1, sz));
    }

    switch (new_args.size()) {
    case 0:
        result = mk_numeral(0, sz);
        return BR_DONE;
    case 1:
        result = new_args[0];
        return BR_DONE;
    default:
        if (m_bv_sort_ac)
            std::sort(new_args.begin(), new_args.end(), ast_to_lt());
        result = m_util.mk_bv_or(new_args.size(), new_args.c_ptr());
        return BR_DONE;
    }
}

br_status bv_rewriter::mk_bv_xor(unsigned num, expr * const * args, expr_ref & result) {
    SASSERT(num > 0);
    if (num == 1) {
        result = args[0];
        return BR_DONE;
    }
    unsigned sz    = get_bv_size(args[0]);
    bool flattened = false;
    ptr_buffer<expr> flat_args;
    if (m_flat) {
        for (unsigned i = 0; i < num; i++) {
            expr * arg = args[i];
            if (m_util.is_bv_xor(arg)) {
                unsigned num2 = to_app(arg)->get_num_args();
                for (unsigned j = 0; j < num2; j++)
                    flat_args.push_back(to_app(arg)->get_arg(j));
            }
            else {
                flat_args.push_back(arg);
            }
        }
        if (flat_args.size() != num) {
            flattened = true;
            num  = flat_args.size();
            args = flat_args.c_ptr();
        }
    }

    expr_fast_mark1  pos_args;
    expr_fast_mark2  neg_args;
    bool merged = false;
    numeral v1, v2;
    unsigned num_coeffs = 0;
    for (unsigned i = 0; i < num; i++) {
        expr * arg = args[i];
        if (is_numeral(arg, v2, sz)) {
            v1 = bitwise_xor(v1, v2);
            num_coeffs++;
            continue;
        }

        if (m_util.is_bv_not(arg)) {
            expr * atom = to_app(arg)->get_arg(0);
            if (neg_args.is_marked(atom)) {
                neg_args.mark(atom, false);
                merged = true;
            }
            else if (pos_args.is_marked(atom)) {
                pos_args.mark(atom, false);
                merged = true;
                v1 = bitwise_xor(v1, rational::power_of_two(sz) - numeral(1));
            }
            else {
                neg_args.mark(atom, true);
            }
        }
        else {
            if (pos_args.is_marked(arg)) {
                pos_args.mark(arg, false);
                merged = true;
            }
            else if (neg_args.is_marked(arg)) {
                neg_args.mark(arg, false);
                merged = true;
                v1 = bitwise_xor(v1, rational::power_of_two(sz) - numeral(1));
            }
            else {
                pos_args.mark(arg, true);
            }
        }
    }

    // XOR is a mask
    // All arguments but one is a numeral.
    //
    // Apply a transformation of the form:
    //
    //   (bvxor a 0011) -->  (concat ((_ extract 3 2) a) ((_ extract 1 0) (bvnot a)))
    //
    if (!v1.is_zero() && num_coeffs == num - 1) {
        // find argument that is not a numeral
        expr * t = nullptr;
        for (unsigned i = 0; i < num; i++) {
            t = args[i];
            if (!is_numeral(t))
                break;
        }
        SASSERT(t != 0);
        numeral two(2);
        expr_ref_buffer exs(m());
        expr_ref not_t(m());
        not_t = m_util.mk_bv_not(t);
        unsigned low = 0;
        unsigned i = 0;
        while (i < sz) {
            while (i < sz && mod(v1, two).is_one()) {
                i++;
                div(v1, two, v1);
            }
            if (i != low) {
                exs.push_back(m_mk_extract(i-1, low, not_t));
                low = i;
            }
            while (i < sz && mod(v1, two).is_zero()) {
                i++;
                div(v1, two, v1);
            }
            if (i != low) {
                exs.push_back(m_mk_extract(i-1, low, t));
                low = i;
            }
        }
        std::reverse(exs.c_ptr(), exs.c_ptr() + exs.size());
        if (exs.size() == 1)
            result = exs[0];
        else
            result = m_util.mk_concat(exs.size(), exs.c_ptr());
        return BR_REWRITE3;
    }

    if (!merged && !flattened && (num_coeffs == 0 || (num_coeffs == 1 && !v1.is_zero() && v1 != (rational::power_of_two(sz) - numeral(1)))) &&
        (!m_bv_sort_ac || is_sorted(num, args)))
        return BR_FAILED;

    ptr_buffer<expr> new_args;
    expr_ref c(m()); // may not be used
    if (!v1.is_zero()) {
        c = mk_numeral(v1, sz);
        new_args.push_back(c);
    }

    for (unsigned i = 0; i < num; i++) {
        expr * arg = args[i];
        if (is_numeral(arg))
            continue;
        if (m_util.is_bv_not(arg)) {
            expr * atom = to_app(arg)->get_arg(0);
            if (neg_args.is_marked(atom)) {
                new_args.push_back(arg);
                neg_args.mark(atom, false);
            }
        }
        else if (pos_args.is_marked(arg)) {
            new_args.push_back(arg);
            pos_args.mark(arg, false);
        }
    }

    switch (new_args.size()) {
    case 0:
        result = mk_numeral(0, sz);
        return BR_DONE;
    case 1:
        result = new_args[0];
        return BR_DONE;
    case 2:
        if (m_util.is_allone(new_args[0])) {
            result = m_util.mk_bv_not(new_args[1]);
            return BR_DONE;
        }
        Z3_fallthrough;
    default:
        if (m_bv_sort_ac)
            std::sort(new_args.begin(), new_args.end(), ast_to_lt());
        result = m_util.mk_bv_xor(new_args.size(), new_args.c_ptr());
        return BR_DONE;
    }
}

br_status bv_rewriter::mk_bv_not(expr * arg, expr_ref & result) {
    if (m_util.is_bv_not(arg)) {
        result = to_app(arg)->get_arg(0);
        return BR_DONE;
    }

    numeral val;
    unsigned bv_size;
    if (is_numeral(arg, val, bv_size)) {
        val = bitwise_not(bv_size, val);
        result = mk_numeral(val, bv_size);
        return BR_DONE;
    }

#if 1
    if (m_util.is_concat(arg)) {
        ptr_buffer<expr> new_args;
        unsigned num = to_app(arg)->get_num_args();
        for (unsigned i = 0; i < num; i++) {
            new_args.push_back(m_util.mk_bv_not(to_app(arg)->get_arg(i)));
        }
        result = m_util.mk_concat(new_args.size(), new_args.c_ptr());
        return BR_REWRITE2;
    }
#endif

    if (m_bvnot2arith) {
        // (bvnot x) --> (bvsub -1 x)
        bv_size = get_bv_size(arg);
        rational minus_one = (rational::power_of_two(bv_size) - numeral(1));
        result = m_util.mk_bv_sub(m_util.mk_numeral(minus_one, bv_size), arg);
        return BR_REWRITE1;
    }

    if (m_bvnot_simpl) {
        expr *s(nullptr), *t(nullptr);
        if (m_util.is_bv_mul(arg, s, t)) {
            // ~(-1 * x) --> (x - 1)
            bv_size = m_util.get_bv_size(s);
            if (m_util.is_allone(s)) {
                rational minus_one = (rational::power_of_two(bv_size) - rational::one());
                result = m_util.mk_bv_add(m_util.mk_numeral(minus_one, bv_size), t);
                return BR_REWRITE1;
            }
            if (m_util.is_allone(t)) {
                rational minus_one = (rational::power_of_two(bv_size) - rational::one());
                result = m_util.mk_bv_add(m_util.mk_numeral(minus_one, bv_size), s);
                return BR_REWRITE1;
            }
        }
        if (m_util.is_bv_add(arg, s, t)) {
            expr_ref ns(m());
            expr_ref nt(m());
            // ~(x + y) --> (~x + ~y + 1) when x and y are easy to negate
            if (is_negatable(t, nt) && is_negatable(s, ns)) {
                bv_size = m_util.get_bv_size(s);
                expr * nargs[3] = { m_util.mk_numeral(rational::one(), bv_size), ns.get(), nt.get() };
                result = m().mk_app(m_util.get_fid(), OP_BADD, 3, nargs);
                return BR_REWRITE1;
            }
        }
    }

    return BR_FAILED;
}

br_status bv_rewriter::mk_bv_and(unsigned num, expr * const * args, expr_ref & result) {
    ptr_buffer<expr> new_args;
    for (unsigned i = 0; i < num; i++) {
        new_args.push_back(m_util.mk_bv_not(args[i]));
    }
    SASSERT(num == new_args.size());
    result = m_util.mk_bv_not(m_util.mk_bv_or(new_args.size(), new_args.c_ptr()));
    return BR_REWRITE3;
}

br_status bv_rewriter::mk_bv_nand(unsigned num, expr * const * args, expr_ref & result) {
    ptr_buffer<expr> new_args;
    for (unsigned i = 0; i < num; i++) {
        new_args.push_back(m_util.mk_bv_not(args[i]));
    }
    result = m_util.mk_bv_or(new_args.size(), new_args.c_ptr());
    return BR_REWRITE2;
}

br_status bv_rewriter::mk_bv_nor(unsigned num, expr * const * args, expr_ref & result) {
    result = m_util.mk_bv_not(m_util.mk_bv_or(num, args));
    return BR_REWRITE2;
}

br_status bv_rewriter::mk_bv_xnor(unsigned num_args, expr * const * args, expr_ref & result) {
    result = m_util.mk_bv_not(m_util.mk_bv_xor(num_args, args));
    return BR_REWRITE2;
}

br_status bv_rewriter::mk_bv_rotate_left(unsigned n, expr * arg, expr_ref & result) {
    unsigned sz = get_bv_size(arg);
    SASSERT(sz > 0);
    n = n % sz;
    if (n == 0 || sz == 1) {
        result = arg;
        return BR_DONE;
    }
    expr * args[2] = { m_mk_extract(sz - n - 1, 0, arg), m_mk_extract(sz - 1, sz - n, arg) };
    result = m_util.mk_concat(2, args);
    return BR_REWRITE2;
}

br_status bv_rewriter::mk_bv_rotate_right(unsigned n, expr * arg, expr_ref & result) {
    unsigned sz = get_bv_size(arg);
    SASSERT(sz > 0);
    n = n % sz;
    return mk_bv_rotate_left(sz - n, arg, result);
}

br_status bv_rewriter::mk_bv_ext_rotate_left(expr * arg1, expr * arg2, expr_ref & result) {
    numeral r2;
    unsigned bv_size;
    if (is_numeral(arg2, r2, bv_size)) {
        unsigned shift = static_cast<unsigned>((r2 % numeral(bv_size)).get_uint64() % static_cast<uint64_t>(bv_size));
        return mk_bv_rotate_left(shift, arg1, result);
    }
    return BR_FAILED;
}

br_status bv_rewriter::mk_bv_ext_rotate_right(expr * arg1, expr * arg2, expr_ref & result) {
    numeral r2;
    unsigned bv_size;
    if (is_numeral(arg2, r2, bv_size)) {
        unsigned shift = static_cast<unsigned>((r2 % numeral(bv_size)).get_uint64() % static_cast<uint64_t>(bv_size));
        return mk_bv_rotate_right(shift, arg1, result);
    }
    return BR_FAILED;
}

br_status bv_rewriter::mk_bv_redor(expr * arg, expr_ref & result) {
    if (is_numeral(arg)) {
        result = m_util.is_zero(arg) ? mk_numeral(0, 1) : mk_numeral(1, 1);
        return BR_DONE;
    }
    return BR_FAILED;
}

br_status bv_rewriter::mk_bv_redand(expr * arg, expr_ref & result) {
    numeral r;
    unsigned bv_size;
    if (is_numeral(arg, r, bv_size)) {
        result = (r == rational::power_of_two(bv_size) - numeral(1)) ? mk_numeral(1, 1) : mk_numeral(0, 1);
        return BR_DONE;
    }
    return BR_FAILED;
}

br_status bv_rewriter::mk_bv_comp(expr * arg1, expr * arg2, expr_ref & result) {
    if (arg1 == arg2) {
        result = mk_numeral(1,1);
        return BR_DONE;
    }

    if (is_numeral(arg1) && is_numeral(arg2)) {
        SASSERT(arg1 != arg2);
        result = mk_numeral(0, 1);
        return BR_DONE;
    }

    result = m().mk_ite(m().mk_eq(arg1, arg2),
                        mk_numeral(1, 1),
                        mk_numeral(0, 1));
    return BR_REWRITE2;
}

br_status bv_rewriter::mk_bv_add(unsigned num_args, expr * const * args, expr_ref & result) {
    br_status st = mk_add_core(num_args, args, result);
    if (st != BR_FAILED && st != BR_DONE)
        return st;
#if 0
    expr * x;
    expr * y;
    if (st == BR_FAILED && num_args == 2) {
        x = args[0]; y = args[1];
    }
    else if (st == BR_DONE && is_add(result) && to_app(result)->get_num_args() == 2) {
        x = to_app(result)->get_arg(0);
        y = to_app(result)->get_arg(1);
    }
    else {
        return st;
    }

    if (!m_util.is_concat(x) && !is_numeral(x))
        return st;
    if (!m_util.is_concat(y) && !is_numeral(y))
        return st;

    unsigned sz = get_bv_size(x);

    for (unsigned i = 0; i < sz; i++) {
        if (!is_zero_bit(x,i) && !is_zero_bit(y,i))
            return st;
    }

    result = m().mk_app(get_fid(), OP_BOR, x, y);
    return BR_REWRITE1;
#else
    unsigned       _num_args;
    expr * const * _args;
    if (st == BR_FAILED) {
        _num_args = num_args;
        _args     = args;
    }
    else if (st == BR_DONE && is_add(result)) {
        _num_args = to_app(result)->get_num_args();
        _args     = to_app(result)->get_args();
    }
    else {
        return st;
    }
    if (_num_args < 2)
        return st;
    unsigned sz = get_bv_size(_args[0]);
    for (unsigned i = 0; i < sz; i++) {
        bool found_non_zero = false;
        for (unsigned j = 0; j < _num_args; j++) {
            if (!is_zero_bit(_args[j], i)) {
                // at most one of the arguments may have a non-zero bit.
                if (found_non_zero)
                    return st;
                found_non_zero = true;
            }
        }
    }
    result = m().mk_app(get_fid(), OP_BOR, _num_args, _args);
    return BR_REWRITE1;
#endif
}

bool bv_rewriter::is_zero_bit(expr * x, unsigned idx) {
    numeral val;
    unsigned bv_size;
 loop:
    if (is_numeral(x, val, bv_size)) {
        if (val.is_zero())
            return true;
        div(val, rational::power_of_two(idx), val);
        return (val % numeral(2)).is_zero();
    }
    if (m_util.is_concat(x)) {
        unsigned i = to_app(x)->get_num_args();
        while (i > 0) {
            --i;
            expr * y = to_app(x)->get_arg(i);
            bv_size = get_bv_size(y);
            if (bv_size <= idx) {
                idx -= bv_size;
            }
            else {
                x = y;
                goto loop;
            }
        }
        UNREACHABLE();
    }
    return false;
}

br_status bv_rewriter::mk_bv_mul(unsigned num_args, expr * const * args, expr_ref & result) {
    br_status st = mk_mul_core(num_args, args, result);
    if (st != BR_FAILED && st != BR_DONE)
        return st;
    expr * x;
    expr * y;
    if (st == BR_FAILED && num_args == 2) {
        x = args[0]; y = args[1];
    }
    else if (st == BR_DONE && is_mul(result) && to_app(result)->get_num_args() == 2) {
        x = to_app(result)->get_arg(0);
        y = to_app(result)->get_arg(1);
    }
    else {
        return st;
    }

    if (m_mul2concat) {
        numeral v;
        unsigned bv_size;
        unsigned shift;
        if (is_numeral(x, v, bv_size) && v.is_power_of_two(shift)) {
            SASSERT(shift >= 1);
            expr * args[2] = {
                m_mk_extract(bv_size-shift-1, 0, y),
                mk_numeral(0, shift)
            };
            result = m_util.mk_concat(2, args);
            return BR_REWRITE2;
        }
    }

    return st;
}

br_status bv_rewriter::mk_bit2bool(expr * n, int idx, expr_ref & result) {
    rational v, bit;
    unsigned sz = 0;
    if (!is_numeral(n, v, sz)) 
        return BR_FAILED;
    if (idx < 0 || idx >= static_cast<int>(sz)) 
        return BR_FAILED;
    div(v, rational::power_of_two(idx), bit);
    mod(bit, rational(2), bit);
    result = m().mk_bool_val(bit.is_one());
    return BR_DONE;
}

br_status bv_rewriter::mk_bit2bool(expr * lhs, expr * rhs, expr_ref & result) {
    unsigned sz = get_bv_size(lhs);
    if (sz != 1)
        return BR_FAILED;
    if (is_numeral(lhs))
        std::swap(lhs, rhs);

    numeral v;

    if (!is_numeral(rhs, v, sz))
        return BR_FAILED;

    if (is_numeral(lhs)) {
        SASSERT(is_numeral(rhs));
        result = m().mk_bool_val(lhs == rhs);
        return BR_DONE;
    }

    if (m().is_ite(lhs)) {
        result = m().mk_ite(to_app(lhs)->get_arg(0),
                            m().mk_eq(to_app(lhs)->get_arg(1), rhs),
                            m().mk_eq(to_app(lhs)->get_arg(2), rhs));
        return BR_REWRITE2;
    }

    if (m_util.is_bv_not(lhs)) {
        SASSERT(v.is_one() || v.is_zero());
        result = m().mk_eq(to_app(lhs)->get_arg(0), mk_numeral(numeral(1) - v, 1));
        return BR_REWRITE1;
    }

    bool is_one = v.is_one();

    expr_ref bit1(m());
    bit1 = is_one ? rhs : mk_numeral(numeral(1), 1);

    if (m_util.is_bv_or(lhs)) {
        ptr_buffer<expr> new_args;
        unsigned num = to_app(lhs)->get_num_args();
        for (unsigned i = 0; i < num; i++) {
            new_args.push_back(m().mk_eq(to_app(lhs)->get_arg(i), bit1));
        }
        result = m().mk_or(new_args.size(), new_args.c_ptr());
        if (is_one) {
            return BR_REWRITE2;
        }
        else {
            result = m().mk_not(result);
            return BR_REWRITE3;
        }
    }


    if (m_util.is_bv_xor(lhs)) {
        ptr_buffer<expr> new_args;
        unsigned num = to_app(lhs)->get_num_args();
        for (unsigned i = 0; i < num; i++) {
            new_args.push_back(m().mk_eq(to_app(lhs)->get_arg(i), bit1));
        }
        // TODO: bool xor is not flat_assoc... must fix that.
        result = m().mk_xor(new_args.size(), new_args.c_ptr());
        if (is_one) {
            return BR_REWRITE2;
        }
        else {
            result = m().mk_not(result);
            return BR_REWRITE3;
        }
    }


    return BR_FAILED;
}

br_status bv_rewriter::mk_blast_eq_value(expr * lhs, expr * rhs, expr_ref & result) {
    unsigned sz = get_bv_size(lhs);
    if (sz == 1)
        return BR_FAILED;
    TRACE("blast_eq_value", tout << "sz: " << sz << "\n" << mk_ismt2_pp(lhs, m()) << "\n";);
    if (is_numeral(lhs))
        std::swap(lhs, rhs);

    numeral v;

    if (!is_numeral(rhs, v, sz))
        return BR_FAILED;
    if (!m_util.is_bv_or(lhs) && !m_util.is_bv_xor(lhs) && !m_util.is_bv_not(lhs))
        return BR_FAILED;

    numeral two(2);
    ptr_buffer<expr> new_args;
    for (unsigned i = 0; i < sz; i++) {
        bool bit0 = (v % two).is_zero();
        new_args.push_back(m().mk_eq(m_mk_extract(i,i, lhs),
                                     mk_numeral(bit0 ? 0 : 1, 1)));
        div(v, two, v);
    }
    result = m().mk_and(new_args.size(), new_args.c_ptr());
    return BR_REWRITE3;
}

br_status bv_rewriter::mk_eq_concat(expr * lhs, expr * rhs, expr_ref & result) {
    SASSERT(m_util.is_concat(lhs) || m_util.is_concat(rhs));
    unsigned num1, num2;
    expr * const * args1, * const * args2;

    if (m_util.is_concat(lhs)) {
        num1  = to_app(lhs)->get_num_args();
        args1 = to_app(lhs)->get_args();
    }
    else {
        num1  = 1;
        args1 = &lhs;
    }

    if (m_util.is_concat(rhs)) {
        num2  = to_app(rhs)->get_num_args();
        args2 = to_app(rhs)->get_args();
    }
    else {
        num2  = 1;
        args2 = &rhs;
    }

    ptr_buffer<expr> new_eqs;
    unsigned low1 = 0;
    unsigned low2 = 0;
    unsigned i1 = num1;
    unsigned i2 = num2;
    while (i1 > 0 && i2 > 0) {
        expr * arg1 = args1[i1-1];
        expr * arg2 = args2[i2-1];
        unsigned sz1  = get_bv_size(arg1);
        unsigned sz2  = get_bv_size(arg2);
        SASSERT(low1 < sz1 && low2 < sz2);
        unsigned rsz1 = sz1 - low1;
        unsigned rsz2 = sz2 - low2;
        if (rsz1 == rsz2) {
            new_eqs.push_back(m().mk_eq(m_mk_extract(sz1 - 1, low1, arg1),
                                        m_mk_extract(sz2 - 1, low2, arg2)));
            low1 = 0;
            low2 = 0;
            --i1;
            --i2;
            continue;
        }
        else if (rsz1 < rsz2) {
            new_eqs.push_back(m().mk_eq(m_mk_extract(sz1  - 1, low1, arg1),
                                        m_mk_extract(rsz1 + low2 - 1, low2, arg2)));
            low1  = 0;
            low2 += rsz1;
            --i1;
        }
        else {
            new_eqs.push_back(m().mk_eq(m_mk_extract(rsz2 + low1 - 1, low1, arg1),
                                        m_mk_extract(sz2  - 1, low2, arg2)));
            low1 += rsz2;
            low2  = 0;
            --i2;
        }
    }
    SASSERT(i1 == 0 && i2 == 0);
    SASSERT(new_eqs.size() >= 1);
    result = m().mk_and(new_eqs.size(), new_eqs.c_ptr());
    return BR_REWRITE3;
}

bool bv_rewriter::is_concat_split_target(expr * t) const {
    return
        m_split_concat_eq ||
        m_util.is_concat(t)  ||
        m_util.is_numeral(t) ||
        m_util.is_bv_or(t);
}

bool bv_rewriter::is_minus_one_times_t(expr * arg) {
    expr * t1, * t2;
    return (m_util.is_bv_mul(arg, t1, t2) && is_minus_one(t1));
}

void bv_rewriter::mk_t1_add_t2_eq_c(expr * t1, expr * t2, expr * c, expr_ref & result) {
    SASSERT(is_numeral(c));
    if (is_minus_one_times_t(t1))
        result = m().mk_eq(t2, m_util.mk_bv_sub(c, t1));
    else
        result = m().mk_eq(t1, m_util.mk_bv_sub(c, t2));
}

#include "ast/ast_pp.h"

bool bv_rewriter::isolate_term(expr* lhs, expr* rhs, expr_ref& result) {
    if (!m_util.is_numeral(lhs) || !is_add(rhs)) {
        std::swap(lhs, rhs);
    }
    if (!m_util.is_numeral(lhs) || !is_add(rhs)) {
        return false;
    }
    unsigned sz = to_app(rhs)->get_num_args();
    expr * t1 = to_app(rhs)->get_arg(0);
    expr_ref t2(m());
    if (sz > 2) {
        t2 = m().mk_app(get_fid(), OP_BADD, sz-1, to_app(rhs)->get_args()+1);
    }
    else {
        SASSERT(sz == 2);
        t2 = to_app(rhs)->get_arg(1);
    }
    mk_t1_add_t2_eq_c(t1, t2, lhs, result);
    return true;
}

bool bv_rewriter::is_add_mul_const(expr* e) const {
    if (!m_util.is_bv_add(e)) {
        return false;
    }
    unsigned num = to_app(e)->get_num_args();
    for (unsigned i = 0; i < num; i++) {
        expr * arg = to_app(e)->get_arg(i);
        expr * c2, * x2;
        if (m_util.is_numeral(arg))
            continue;
        if (m_util.is_bv_mul(arg, c2, x2) && m_util.is_numeral(c2))
            continue;
        return false;
    }
    return true;
}

bool bv_rewriter::is_concat_target(expr* lhs, expr* rhs) const {
    return
        (m_util.is_concat(lhs) && is_concat_split_target(rhs)) ||
        (m_util.is_concat(rhs) && is_concat_split_target(lhs));
}

bool bv_rewriter::has_numeral(app* a) const {
    for (unsigned i = 0; i < a->get_num_args(); ++i) {
        if (is_numeral(a->get_arg(i))) {
            return true;
        }
    }
    return false;
}

br_status bv_rewriter::mk_mul_eq(expr * lhs, expr * rhs, expr_ref & result) {

    expr * c, * x;
    numeral c_val, c_inv_val;
    unsigned sz;
    if (m_util.is_bv_mul(lhs, c, x) &&
        m_util.is_numeral(c, c_val, sz) &&
        m_util.mult_inverse(c_val, sz, c_inv_val)) {

        SASSERT(m_util.norm(c_val * c_inv_val, sz).is_one());

        numeral rhs_val;
        // c * x = a
        if (m_util.is_numeral(rhs, rhs_val, sz)) {
            // x = c_inv * a
            result = m().mk_eq(x, m_util.mk_numeral(c_inv_val * rhs_val, sz));
            return BR_REWRITE1;
        }

        expr * c2, * x2;
        numeral c2_val;
        // c * x = c2 * x2
        if (m_util.is_bv_mul(rhs, c2, x2) && m_util.is_numeral(c2, c2_val, sz)) {
            // x = c_inv * c2 * x2
            numeral new_c2 = m_util.norm(c_inv_val * c2_val, sz);
            if (new_c2.is_one())
                result = m().mk_eq(x, x2);
            else
                result = m().mk_eq(x, m_util.mk_bv_mul(m_util.mk_numeral(c_inv_val * c2_val, sz), x2));
            return BR_REWRITE1;
        }

        // c * x =  t_1 + ... + t_n
        // and t_i's have non-unary coefficients (this condition is used to make sure we are actually reducing the number of multipliers).
        if (is_add_mul_const(rhs)) {
            // Potential problem: this simplification may increase the number of adders by reducing the amount of sharing.
            result = m().mk_eq(x, m_util.mk_bv_mul(m_util.mk_numeral(c_inv_val, sz), rhs));
            return BR_REWRITE2;
        }
    }
    if (m_util.is_numeral(lhs, c_val, sz) && is_add_mul_const(rhs)) {
        unsigned num_args = to_app(rhs)->get_num_args();
        unsigned i = 0;
        expr* c2, *x2;
        numeral c2_val, c2_inv_val;
        bool found = false;
        for (; !found && i < num_args; ++i) {
            expr* arg = to_app(rhs)->get_arg(i);
            if (m_util.is_bv_mul(arg, c2, x2) && m_util.is_numeral(c2, c2_val, sz) &&
                m_util.mult_inverse(c2_val, sz, c2_inv_val)) {
                found = true;
            }
        }
        if (found) {
            result = m().mk_eq(m_util.mk_numeral(c2_inv_val*c_val, sz),
                               m_util.mk_bv_mul(m_util.mk_numeral(c2_inv_val, sz), rhs));
            return BR_REWRITE3;
        }
    }
    return BR_FAILED;
}

bool bv_rewriter::is_urem_any(expr * e, expr * & dividend,  expr * & divisor) {
    if (!m_util.is_bv_urem(e) && !m_util.is_bv_uremi(e))
        return false;
    const app * const a = to_app(e);
    SASSERT(a->get_num_args() == 2);
    dividend = a->get_arg(0);
    divisor = a->get_arg(1);
    return true;
}

br_status bv_rewriter::mk_eq_core(expr * lhs, expr * rhs, expr_ref & result) {
    if (lhs == rhs) {
        result = m().mk_true();
        return BR_DONE;
    }

    if (is_numeral(lhs) && is_numeral(rhs)) {
        result = m().mk_false();
        return BR_DONE;
    }

    bool swapped = false;
    if (is_numeral(lhs)) {
        swapped = true;
        std::swap(lhs, rhs);
    }

    br_status st;
    if (m_bit2bool) {
        st = mk_bit2bool(lhs, rhs, result);
        if (st != BR_FAILED)
            return st;
    }

    if (m_trailing) {
        st = m_rm_trailing.eq_remove_trailing(lhs, rhs, result);
        m_rm_trailing.reset_cache(1 << 12);
        if (st != BR_FAILED) {
            TRACE("eq_remove_trailing", tout << mk_ismt2_pp(lhs, m()) << "\n=\n" << mk_ismt2_pp(rhs, m()) << "\n----->\n" << mk_ismt2_pp(result, m()) << "\n";);
            return st;
        }
    }

    st = mk_mul_eq(lhs, rhs, result);
    if (st != BR_FAILED) {
        TRACE("mk_mul_eq", tout << mk_ismt2_pp(lhs, m()) << "\n=\n" << mk_ismt2_pp(rhs, m()) << "\n----->\n" << mk_ismt2_pp(result,m()) << "\n";);
        return st;
    }

    st = mk_mul_eq(rhs, lhs, result);
    if (st != BR_FAILED) {
        TRACE("mk_mul_eq", tout << mk_ismt2_pp(lhs, m()) << "\n=\n" << mk_ismt2_pp(rhs, m()) << "\n----->\n" << mk_ismt2_pp(result,m()) << "\n";);
        return st;
    }

    if (m_blast_eq_value) {
        st = mk_blast_eq_value(lhs, rhs, result);
        if (st != BR_FAILED)
            return st;
    }

    if (m_urem_simpl) {
        expr * dividend;
        expr * divisor;
        numeral divisor_val, rhs_val;
        unsigned divisor_sz, rhs_sz;
        if (is_urem_any(lhs, dividend, divisor)
            && is_numeral(rhs, rhs_val, rhs_sz)
            && is_numeral(divisor, divisor_val, divisor_sz)) {
            if (rhs_val >= divisor_val) {//(= (bvurem x c1) c2) where c2 >= c1
                result = m().mk_false();
                return BR_DONE;
            }
            if ((divisor_val + rhs_val) >= rational::power_of_two(divisor_sz)) {//(= (bvurem x c1) c2) where c1+c2 >= 2^width
                result = m().mk_eq(dividend, rhs);
                return BR_REWRITE2;
            }
        }
    }

    expr_ref new_lhs(m());
    expr_ref new_rhs(m());

    if (m_util.is_bv_add(lhs) || m_util.is_bv_mul(lhs) || m_util.is_bv_add(rhs) || m_util.is_bv_mul(rhs)) {
        st = cancel_monomials(lhs, rhs, false, new_lhs, new_rhs);
        if (st != BR_FAILED) {
            if (is_numeral(new_lhs) && is_numeral(new_rhs)) {
                result = m().mk_bool_val(new_lhs == new_rhs);
                return BR_DONE;
            }
            lhs = new_lhs;
            rhs = new_rhs;
        }

        // Try to rewrite t1 + t2 = c --> t1 = c - t2
        // Reason: it is much cheaper to bit-blast.
        if (isolate_term(lhs, rhs, result)) {
            return BR_REWRITE2;
        }
        if (is_concat_target(lhs, rhs)) {
            return mk_eq_concat(lhs, rhs, result);
        }

        if (st != BR_FAILED) {
            result = m().mk_eq(lhs, rhs);
            return BR_DONE;
        }
    }

    if (is_concat_target(lhs, rhs)) {
        return mk_eq_concat(lhs, rhs, result);
    }

    if (swapped) {
        result = m().mk_eq(lhs, rhs);
        return BR_DONE;
    }

    return BR_FAILED;
}


br_status bv_rewriter::mk_mkbv(unsigned num, expr * const * args, expr_ref & result) {
    if (m_mkbv2num) {
        unsigned i;
        for (i = 0; i < num; i++)
            if (!m().is_true(args[i]) && !m().is_false(args[i]))
                return BR_FAILED;
        numeral val;
        numeral two(2);
        i = num;
        while (i > 0) {
            --i;
            val *= two;
            if (m().is_true(args[i]))
                val++;
        }
        result = mk_numeral(val, num);
        return BR_DONE;
    }
    return BR_FAILED;
}

br_status bv_rewriter::mk_ite_core(expr * c, expr * t, expr * e, expr_ref & result) {
    TRACE("bv_ite", tout << "mk_ite_core:\n" << mk_ismt2_pp(c, m()) << "?\n"
            << mk_ismt2_pp(t, m()) << "\n:" << mk_ismt2_pp(e, m()) << "\n";);
    if (m().are_equal(t, e)) {
        result = e;
        return BR_REWRITE1;
    }
    if (m().is_not(c)) {
        result = m().mk_ite(to_app(c)->get_arg(0), e, t);
        return BR_REWRITE1;
    }

    if (m_ite2id && m().is_eq(c) && is_bv(t) && is_bv(e)) {
        // detect when ite is actually some simple function based on the pattern (lhs=rhs) ? t : e
        expr * lhs = to_app(c)->get_arg(0);
        expr * rhs = to_app(c)->get_arg(1);

        if (is_bv(rhs)) {
            if (is_numeral(lhs))
                std::swap(lhs, rhs);

            if (   (m().are_equal(lhs, t) && m().are_equal(rhs, e))
                || (m().are_equal(lhs, e) && m().are_equal(rhs, t))) {
                // (a = b ? a : b) is b.  (a = b ? b : a) is a
                result = e;
                return BR_REWRITE1;
            }

            const unsigned sz = m_util.get_bv_size(rhs);
            if (sz == 1) { // detect (lhs = N) ? C : D, where N, C, D are 1 bit numerals
                numeral rhs_n, e_n, t_n;
                unsigned rhs_sz, e_sz, t_sz;
                if (is_numeral(rhs, rhs_n, rhs_sz)
                    && is_numeral(t, t_n, t_sz) && is_numeral(e, e_n, e_sz)) {
                    if (t_sz == 1) {
                        SASSERT(rhs_sz == sz && e_sz == sz && t_sz == sz);
                        SASSERT(!m().are_equal(t, e));
                        result = m().are_equal(rhs, t) ? lhs : m_util.mk_bv_not(lhs);
                        return BR_REWRITE1;
                    }
                }
            }
        }


    }
    return BR_FAILED;
}

br_status bv_rewriter::mk_bvsmul_no_overflow(unsigned num, expr * const * args, expr_ref & result) {
    SASSERT(num == 2);
    unsigned bv_sz;
    rational a0_val, a1_val;

    bool is_num1 = is_numeral(args[0], a0_val, bv_sz);
    bool is_num2 = is_numeral(args[1], a1_val, bv_sz);
    if (is_num1 && (a0_val.is_zero() || a0_val.is_one())) {
        result = m().mk_true();
        return BR_DONE;
    }
    if (is_num2 && (a1_val.is_zero() || a1_val.is_one())) {
        result = m().mk_true();
        return BR_DONE;
    }

    if (is_num1 && is_num2) {
        rational mr = a0_val * a1_val;
        rational lim = rational::power_of_two(bv_sz-1);
        result = m().mk_bool_val(mr < lim);
        return BR_DONE;
    }

    return BR_FAILED;
}

br_status bv_rewriter::mk_bvumul_no_overflow(unsigned num, expr * const * args, expr_ref & result) {
    SASSERT(num == 2);
    unsigned bv_sz;
    rational a0_val, a1_val;

    bool is_num1 = is_numeral(args[0], a0_val, bv_sz);
    bool is_num2 = is_numeral(args[1], a1_val, bv_sz);
    if (is_num1 && (a0_val.is_zero() || a0_val.is_one())) {
        result = m().mk_true();
        return BR_DONE;
    }
    if (is_num2 && (a1_val.is_zero() || a1_val.is_one())) {
        result = m().mk_true();
        return BR_DONE;
    }

    if (is_num1 && is_num2) {
        rational mr = a0_val * a1_val;
        rational lim = rational::power_of_two(bv_sz);
        result = m().mk_bool_val(mr < lim);
        return BR_DONE;
    }

    return BR_FAILED;
}

br_status bv_rewriter::mk_bvsmul_no_underflow(unsigned num, expr * const * args, expr_ref & result) {
    SASSERT(num == 2);
    unsigned bv_sz;
    rational a0_val, a1_val;

    bool is_num1 = is_numeral(args[0], a0_val, bv_sz);
    bool is_num2 = is_numeral(args[1], a1_val, bv_sz);
    if (is_num1 && (a0_val.is_zero() || a0_val.is_one())) {
        result = m().mk_true();
        return BR_DONE;
    }
    if (is_num2 && (a1_val.is_zero() || a1_val.is_one())) {
        result = m().mk_true();
        return BR_DONE;
    }

    if (is_num1 && is_num2) {
        rational ul = rational::power_of_two(bv_sz);
        rational lim = rational::power_of_two(bv_sz-1);
        if (a0_val >= lim) a0_val -= ul;
        if (a1_val >= lim) a1_val -= ul;        
        rational mr = a0_val * a1_val;
        rational neg_lim = -lim;
        TRACE("bv_rewriter_bvsmul_no_underflow", tout << "a0:" << a0_val << " a1:" << a1_val << " mr:" << mr << " neg_lim:" << neg_lim << std::endl;);
        result = m().mk_bool_val(mr >= neg_lim);
        return BR_DONE;
    }

    return BR_FAILED;
}


template class poly_rewriter<bv_rewriter_core>;
