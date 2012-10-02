/*++
Copyright (c) 2006 Microsoft Corporation

Module Name:

    eager_bit_blaster.cpp

Abstract:

    <abstract>

Author:

    Leonardo de Moura (leonardo) 2008-10-02.

Revision History:

--*/

#include"ast_ll_pp.h"
#include"eager_bit_blaster.h"

eager_bit_blaster::basic_plugin::basic_plugin(ast_manager & m, eager_bit_blaster::bv_plugin & p, basic_simplifier_plugin & s):
    simplifier_plugin(symbol("basic"), m),
    m_main(p),
    m_s(s) {
}

eager_bit_blaster::basic_plugin::~basic_plugin() {
}

bool eager_bit_blaster::basic_plugin::reduce(func_decl * f, unsigned num_args, expr * const * args, expr_ref & result) {
    if (f->get_decl_kind() == OP_ITE) {
        SASSERT(num_args == 3);
        return m_main.reduce_ite(args[0], args[1], args[2], result);
    }
    else if (f->get_decl_kind() == OP_NOT) {
        // the internalizer assumes there is not double negation (not (not x))
        SASSERT(num_args == 1);
        m_s.mk_not(args[0], result);
        return true;
    }
    return false;
}

eager_bit_blaster::bv_plugin::bv_plugin(ast_manager & m, bit_blaster_params const & p):
    simplifier_plugin(symbol("bv"), m),
    m_util(m), 
    m_bb(m, p),
    m_s(m) {
}
    
eager_bit_blaster::bv_plugin::~bv_plugin() {
}

void eager_bit_blaster::bv_plugin::get_bits(expr * n, expr_ref_vector & out_bits) {
    rational val;
    unsigned bv_size;
    if (m_util.is_numeral(n, val, bv_size)) {
        TRACE("eager_bb_bug", tout << "bv_size: " << bv_size << "\n";);
        m_bb.num2bits(val, bv_size, out_bits);
        SASSERT(out_bits.size() == bv_size);
    }
    else if (m_util.is_mkbv(n)) {
        out_bits.append(to_app(n)->get_num_args(), to_app(n)->get_args());
    }
    else {
        unsigned bv_size = m_util.get_bv_size(n);
        for (unsigned i = 0; i < bv_size; i++) {
            parameter p(i);
            out_bits.push_back(m_manager.mk_app(get_family_id(), OP_BIT2BOOL, 1, &p, 1, &n));
        }
        SASSERT(bv_size == out_bits.size());
    }
}

inline app * eager_bit_blaster::bv_plugin::mk_mkbv(expr_ref_vector const & bits) {
#ifdef Z3DEBUG
    for (unsigned i = 0; i < bits.size(); i++) {
        expr * b = bits.get(i);
        SASSERT(!m_manager.is_not(b) || !m_manager.is_not(to_app(b)->get_arg(0)));
    }
#endif
    return m_manager.mk_app(get_family_id(), OP_MKBV, bits.size(), bits.c_ptr());
}

#define MK_UNARY_REDUCE(OP, BB_OP)                                      \
void eager_bit_blaster::bv_plugin::OP(expr * arg, expr_ref & result) {  \
    expr_ref_vector bits(m_manager);                                    \
    get_bits(arg, bits);                                                \
    expr_ref_vector out_bits(m_manager);                                \
    m_bb.BB_OP(bits.size(), bits.c_ptr(), out_bits);                    \
    result = mk_mkbv(out_bits);                                         \
}

#define MK_BIN_REDUCE(OP, BB_OP)                                                        \
void eager_bit_blaster::bv_plugin::OP(expr * arg1, expr * arg2, expr_ref & result) {    \
    expr_ref_vector bits1(m_manager);                                                   \
    expr_ref_vector bits2(m_manager);                                                   \
    get_bits(arg1, bits1);                                                              \
    get_bits(arg2, bits2);                                                              \
    expr_ref_vector out_bits(m_manager);                                                \
    m_bb.BB_OP(bits1.size(), bits1.c_ptr(), bits2.c_ptr(), out_bits);                   \
    result = mk_mkbv(out_bits);                                                         \
}

#define MK_BIN_AC_FLAT_REDUCE(OP, BIN_OP, S_OP, BB_OP)                                                  \
MK_BIN_REDUCE(BIN_OP, BB_OP);                                                                           \
void eager_bit_blaster::bv_plugin::OP(unsigned num_args, expr * const * args, expr_ref & result) {      \
    SASSERT(num_args > 0);                                                                              \
    if (num_args == 2) {                                                                                \
        BIN_OP(args[0], args[1], result);                                                               \
        return;                                                                                         \
    }                                                                                                   \
                                                                                                        \
    ptr_buffer<expr_ref_vector> args_bits;                                                              \
    for (unsigned i = 0; i < num_args; i++) {                                                           \
        expr_ref_vector * bits = alloc(expr_ref_vector, m_manager);                                     \
        get_bits(args[i], *bits);                                                                       \
        args_bits.push_back(bits);                                                                      \
    }                                                                                                   \
                                                                                                        \
    unsigned bv_size = m_util.get_bv_size(args[0]);                                                     \
    expr_ref_vector new_bits(m_manager);                                                                \
    for (unsigned i = 0; i < bv_size; i++) {                                                            \
        expr_ref_vector arg_bits(m_manager);                                                            \
        for (unsigned j = 0; j < num_args; j++)                                                         \
            arg_bits.push_back(args_bits[j]->get(i));                                                   \
        expr_ref new_bit(m_manager);                                                                    \
        m_s.S_OP(arg_bits.size(), arg_bits.c_ptr(), new_bit);                                           \
        new_bits.push_back(new_bit);                                                                    \
    }                                                                                                   \
    result = mk_mkbv(new_bits);                                                                         \
    std::for_each(args_bits.begin(), args_bits.end(), delete_proc<expr_ref_vector>());                  \
}

#define MK_BIN_AC_REDUCE(OP, BIN_OP, BB_OP)                                                             \
MK_BIN_REDUCE(BIN_OP, BB_OP);                                                                           \
void eager_bit_blaster::bv_plugin::OP(unsigned num_args, expr * const * args, expr_ref & result) {      \
    SASSERT(num_args > 0);                                                                              \
    result = args[0];                                                                                   \
    for (unsigned i = 1; i < num_args; i++) {                                                           \
        expr_ref new_result(m_manager);                                                                 \
        BIN_OP(result.get(), args[i], new_result);                                                      \
        result = new_result;                                                                            \
    }                                                                                                   \
}

#define MK_BIN_PRED_REDUCE(OP, BB_OP)                                                   \
void eager_bit_blaster::bv_plugin::OP(expr * arg1, expr * arg2, expr_ref & result) {    \
    expr_ref_vector bits1(m_manager);                                                   \
    expr_ref_vector bits2(m_manager);                                                   \
    get_bits(arg1, bits1);                                                              \
    get_bits(arg2, bits2);                                                              \
    m_bb.BB_OP(bits1.size(), bits1.c_ptr(), bits2.c_ptr(), result);                     \
}

#define MK_PARAMETRIC_UNARY_REDUCE(OP, BB_OP)                                           \
void eager_bit_blaster::bv_plugin::OP(expr * arg, unsigned n, expr_ref & result) {      \
    expr_ref_vector bits(m_manager);                                                    \
    get_bits(arg, bits);                                                                \
    expr_ref_vector out_bits(m_manager);                                                \
    m_bb.BB_OP(bits.size(), bits.c_ptr(), n, out_bits);                                 \
    result = mk_mkbv(out_bits);                                                         \
}

MK_UNARY_REDUCE(reduce_not, mk_not);
MK_BIN_AC_FLAT_REDUCE(reduce_or, reduce_bin_or, mk_or, mk_or);
MK_BIN_AC_FLAT_REDUCE(reduce_and, reduce_bin_and, mk_and, mk_and);
MK_BIN_AC_FLAT_REDUCE(reduce_nor, reduce_bin_nor, mk_nor, mk_nor);
MK_BIN_AC_FLAT_REDUCE(reduce_nand, reduce_bin_nand, mk_nand, mk_nand);
MK_BIN_REDUCE(reduce_xor,  mk_xor);
MK_BIN_REDUCE(reduce_xnor, mk_xnor);
MK_UNARY_REDUCE(reduce_neg, mk_neg);
MK_BIN_AC_REDUCE(reduce_add, reduce_bin_add, mk_adder);
MK_BIN_AC_REDUCE(reduce_mul, reduce_bin_mul, mk_multiplier);
MK_BIN_PRED_REDUCE(reduce_sle, mk_sle);
MK_BIN_PRED_REDUCE(reduce_ule, mk_ule);
MK_PARAMETRIC_UNARY_REDUCE(reduce_rotate_left, mk_rotate_left);
MK_PARAMETRIC_UNARY_REDUCE(reduce_rotate_right, mk_rotate_right);
MK_PARAMETRIC_UNARY_REDUCE(reduce_sign_extend, mk_sign_extend);
MK_PARAMETRIC_UNARY_REDUCE(reduce_zero_extend, mk_zero_extend);
MK_UNARY_REDUCE(reduce_redor, mk_redor);
MK_UNARY_REDUCE(reduce_redand, mk_redand);
MK_BIN_REDUCE(reduce_shl, mk_shl);
MK_BIN_REDUCE(reduce_ashr, mk_ashr);
MK_BIN_REDUCE(reduce_lshr, mk_lshr);
MK_BIN_REDUCE(reduce_comp, mk_comp);
MK_BIN_REDUCE(reduce_udiv, mk_udiv);
MK_BIN_REDUCE(reduce_urem, mk_urem);
MK_BIN_REDUCE(reduce_sdiv, mk_sdiv);
MK_BIN_REDUCE(reduce_srem, mk_srem);
MK_BIN_REDUCE(reduce_smod, mk_smod);

void eager_bit_blaster::bv_plugin::reduce_extract(unsigned start, unsigned end, expr * arg, expr_ref & result) {
    expr_ref_vector bits(m_manager);
    get_bits(arg, bits);
    expr_ref_vector out_bits(m_manager);
    for (unsigned i = start; i <= end; ++i)
        out_bits.push_back(bits.get(i));
    result = mk_mkbv(out_bits);
}

void eager_bit_blaster::bv_plugin::reduce_concat(unsigned num_args, expr * const * args, expr_ref & result) {
    expr_ref_vector out_bits(m_manager);
    unsigned i = num_args;
    while (i > 0) {
        i--;
        expr_ref_vector bits(m_manager);
        get_bits(args[i], bits);
        out_bits.append(bits.size(), bits.c_ptr());
    }
    result = mk_mkbv(out_bits);
}

bool eager_bit_blaster::bv_plugin::reduce_ite(expr * arg1, expr * arg2, expr * arg3, expr_ref & result) {
    sort * s = m_manager.get_sort(arg2);
    if (!m_util.is_bv_sort(s))
        return false;
    expr_ref_vector bits1(m_manager);
    expr_ref_vector bits2(m_manager);
    get_bits(arg2, bits1);
    get_bits(arg3, bits2);
    SASSERT(bits1.size() == bits2.size());
    expr_ref_vector out_bits(m_manager);
    unsigned bv_size = bits1.size();
    for (unsigned i = 0; i < bv_size; i++) {
        expr_ref new_bit(m_manager);
        m_s.mk_ite(arg1, bits1.get(i), bits2.get(i), new_bit);
        out_bits.push_back(new_bit);
    }
    result = mk_mkbv(out_bits);
    return true;
}

bool eager_bit_blaster::bv_plugin::reduce(func_decl * f, unsigned num_args, expr * const * args, expr_ref & result) {
    bv_op_kind k = static_cast<bv_op_kind>(f->get_decl_kind());
    switch (k) {
    case OP_BNOT:
        SASSERT(num_args == 1);
        reduce_not(args[0], result);
        return true;
    case OP_BOR:
        reduce_or(num_args, args, result);
        return true;
    case OP_BAND:
        reduce_and(num_args, args, result);
        return true;
    case OP_BNOR:
        reduce_nor(num_args, args, result);
        return true;
    case OP_BNAND:
        reduce_nand(num_args, args, result);
        return true;
    case OP_BXOR:
        SASSERT(num_args == 2);
        reduce_xor(args[0], args[1], result);
        return true;
    case OP_BXNOR:
        SASSERT(num_args == 2);
        reduce_xnor(args[0], args[1], result);
        return true;
    case OP_BNEG:
        SASSERT(num_args == 1);
        reduce_neg(args[0], result);
        return true;
    case OP_BADD:
        reduce_add(num_args, args, result);
        return true;
    case OP_BMUL:
        reduce_mul(num_args, args, result);
        return true;
    case OP_BIT1:
    case OP_BIT0:
    case OP_BSUB:
        // I'm assuming the expressions were simplified before invoking this method.
        UNREACHABLE();
        return false;
    case OP_BSDIV:
    case OP_BUDIV:
    case OP_BSREM:
    case OP_BUREM:
    case OP_BSMOD:
        // I'm assuming the expressions were simplified before invoking this method.
        UNREACHABLE();
        return false;
    case OP_BSDIV0:
    case OP_BUDIV0:
    case OP_BSREM0:
    case OP_BUREM0:
    case OP_BSMOD0:
        // do nothing... these are uninterpreted
        return true;
    case OP_BSDIV_I:
        SASSERT(num_args == 2);
        reduce_sdiv(args[0], args[1], result);
        return true;
    case OP_BUDIV_I:
        SASSERT(num_args == 2);
        reduce_udiv(args[0], args[1], result);
        return true;
    case OP_BSREM_I:
        SASSERT(num_args == 2);
        reduce_srem(args[0], args[1], result);
        return true;
    case OP_BUREM_I:
        SASSERT(num_args == 2);
        reduce_urem(args[0], args[1], result);
        return true;
    case OP_BSMOD_I:
        SASSERT(num_args == 2);
        reduce_smod(args[0], args[1], result);
        return true;
    case OP_ULEQ:
        SASSERT(num_args == 2);
        reduce_ule(args[0], args[1], result);
        return true;
    case OP_SLEQ:
        SASSERT(num_args == 2);
        reduce_sle(args[0], args[1], result);
        return true;
    case OP_UGEQ:
    case OP_SGEQ:
    case OP_ULT:
    case OP_SLT:
    case OP_UGT:
    case OP_SGT:
        // I'm assuming the expressions were simplified before invoking this method.
        UNREACHABLE();
        return false;
    case OP_EXTRACT:
        SASSERT(num_args == 1);
        reduce_extract(f->get_parameter(1).get_int(), f->get_parameter(0).get_int(), args[0], result);
        return true;
    case OP_CONCAT:
        reduce_concat(num_args, args, result);
        return true;
    case OP_SIGN_EXT:
        SASSERT(num_args == 1);
        reduce_sign_extend(args[0], f->get_parameter(0).get_int(), result);
        return true;
    case OP_ZERO_EXT:
        SASSERT(num_args == 1);
        reduce_zero_extend(args[0], f->get_parameter(0).get_int(), result);
        return true;
    case OP_REPEAT:
        UNREACHABLE();
        return false;
    case OP_BREDOR:
        SASSERT(num_args == 1);
        reduce_redor(args[0], result);
        return true;
    case OP_BREDAND:
        SASSERT(num_args == 1);
        reduce_redand(args[0], result);
        return true;
    case OP_BCOMP:
        SASSERT(num_args == 2);
        reduce_comp(args[0], args[1], result);
        return true;
    case OP_BSHL:
        SASSERT(num_args == 2);
        reduce_shl(args[0], args[1], result);
        return true;
    case OP_BLSHR:
        SASSERT(num_args == 2);
        reduce_lshr(args[0], args[1], result);
        return true;
    case OP_BASHR:
        SASSERT(num_args == 2);
        reduce_ashr(args[0], args[1], result);
        return true;
    case OP_ROTATE_LEFT:
        SASSERT(num_args == 1);
        reduce_rotate_left(args[0], f->get_parameter(0).get_int(), result);
        return true;
    case OP_ROTATE_RIGHT:
        SASSERT(num_args == 1);
        reduce_rotate_right(args[0], f->get_parameter(0).get_int(), result);
        return true;
    default:
        return false;
    }
}

bool eager_bit_blaster::bv_plugin::reduce_eq(expr * lhs, expr * rhs, expr_ref & result) {
    TRACE("eager_bb_eq", tout << mk_ll_pp(lhs, m_manager) << "\n" << mk_ll_pp(rhs, m_manager) << "\n";);
    SASSERT(m_util.get_bv_size(lhs) == m_util.get_bv_size(rhs));
    expr_ref_vector bits1(m_manager);                                                   
    expr_ref_vector bits2(m_manager);                                                   
    get_bits(lhs, bits1);                                                              
    get_bits(rhs, bits2); 
    SASSERT(bits1.size() == bits2.size());
    m_bb.mk_eq(bits1.size(), bits1.c_ptr(), bits2.c_ptr(), result);
    return true;
}

bool eager_bit_blaster::bv_plugin::reduce_distinct(unsigned num_args, expr * const * args, expr_ref & result) {
    if (num_args <= 1) {
        result = m_manager.mk_true();
    }
    if (num_args == 2) {
        expr_ref tmp(m_manager);
        reduce_eq(args[0], args[1], tmp);
        m_s.mk_not(tmp, result);
    }
    else {
        expr_ref_vector new_args(m_manager);
        for (unsigned i = 0; i < num_args - 1; i++) {
            expr * a1 = args[i];
            for (unsigned j = i + 1; j < num_args; j++) {
                expr * a2 = args[j];
                expr_ref tmp1(m_manager);
                reduce_eq(a1, a2, tmp1);
                expr_ref tmp2(m_manager);
                m_s.mk_not(tmp1, tmp2);
                new_args.push_back(tmp2);
            }
        }
        m_s.mk_and(new_args.size(), new_args.c_ptr(), result);
    }
    return true;
}

eager_bit_blaster::eager_bit_blaster(ast_manager & m, bit_blaster_params const & p):
    m_simplifier(m) {
    m_simplifier.enable_ac_support(false);
    bv_plugin * bv_p = alloc(bv_plugin, m, p);
    m_simplifier.register_plugin(bv_p);
    m_simplifier.register_plugin(alloc(basic_plugin, m, *bv_p, bv_p->get_basic_simplifier()));
}

void eager_bit_blaster::operator()(expr * s, expr_ref & r, proof_ref & p) {
    m_simplifier.operator()(s, r, p);
}

