/*++
Copyright (c) 2011 Microsoft Corporation

Module Name:

    bv1_blaster.cpp

Abstract:

    Simplifier for "blasting" bit-vectors of size n into bit-vectors of size 1.
    This simplifier only supports concat and extract operators.
    This transformation is useful for handling benchmarks that contain
    many BV equalities.

    Remark: other operators can be mapped into concat/extract by using
    the simplifiers.

Author:

    Leonardo (leonardo) 2011-10-25

--*/
#include "ast/simplifiers/bv1_blaster.h"
#include "ast/ast_util.h"
#include "ast/rewriter/bv_rewriter.h"
#include "ast/rewriter/rewriter_types.h"
#include "util/common_msgs.h"

bv1_blaster_simplifier::rw_cfg::rw_cfg(ast_manager& m, params_ref const& p) :
    m_manager(m),
    m_util(m),
    m_saved(m),
    m_bit1(m),
    m_bit0(m) {
    m_bit1 = butil().mk_numeral(rational(1), 1);
    m_bit0 = butil().mk_numeral(rational(0), 1);
    updt_params(p);
}

void bv1_blaster_simplifier::rw_cfg::updt_params(params_ref const& p) {
    m_max_memory = megabytes_to_bytes(p.get_uint("max_memory", UINT_MAX));
    m_max_steps  = p.get_uint("max_steps", UINT_MAX);
}

bool bv1_blaster_simplifier::rw_cfg::max_steps_exceeded(unsigned num_steps) const {
    if (memory::get_allocation_size() > m_max_memory)
        throw rewriter_exception(Z3_MAX_MEMORY_MSG);
    return num_steps > m_max_steps;
}

void bv1_blaster_simplifier::rw_cfg::get_bits(expr* arg, bit_buffer& bits) {
    SASSERT(butil().is_concat(arg) || butil().get_bv_size(arg) == 1);
    if (butil().is_concat(arg))
        bits.append(to_app(arg)->get_num_args(), to_app(arg)->get_args());
    else
        bits.push_back(arg);
}

void bv1_blaster_simplifier::rw_cfg::mk_const(func_decl* f, expr_ref& result) {
    SASSERT(f->get_family_id() == null_family_id);
    SASSERT(f->get_arity() == 0);
    expr* r;
    if (m_const2bits.find(f, r)) {
        result = r;
        return;
    }
    sort* s = f->get_range();
    SASSERT(butil().is_bv_sort(s));
    unsigned bv_size = butil().get_bv_size(s);
    if (bv_size == 1) {
        result = m().mk_const(f);
        return;
    }
    sort* b = butil().mk_sort(1);
    ptr_buffer<expr> bits;
    for (unsigned i = 0; i < bv_size; ++i) {
        bits.push_back(m().mk_fresh_const(nullptr, b));
        m_newbits.push_back(to_app(bits.back())->get_decl());
        m_saved.push_back(m_newbits.back());
    }
    r = butil().mk_concat(bits.size(), bits.data());
    m_saved.push_back(r);
    m_saved.push_back(f);
    m_const2bits.insert(f, r);
    result = r;
}

void bv1_blaster_simplifier::rw_cfg::blast_bv_term(expr* t, expr_ref& result) {
    bit_buffer bits;
    unsigned bv_size = butil().get_bv_size(t);
    if (bv_size == 1) {
        result = t;
        return;
    }
    unsigned i = bv_size;
    while (i > 0) {
        --i;
        bits.push_back(butil().mk_extract(i, i, t));
    }
    result = butil().mk_concat(bits.size(), bits.data());
}

void bv1_blaster_simplifier::rw_cfg::reduce_eq(expr* arg1, expr* arg2, expr_ref& result) {
    bit_buffer bits1;
    bit_buffer bits2;
    get_bits(arg1, bits1);
    get_bits(arg2, bits2);
    SASSERT(bits1.size() == bits2.size());
    bit_buffer new_eqs;
    unsigned i = bits1.size();
    while (i > 0) {
        --i;
        new_eqs.push_back(m().mk_eq(bits1[i], bits2[i]));
    }
    result = mk_and(m(), new_eqs.size(), new_eqs.data());
}

void bv1_blaster_simplifier::rw_cfg::reduce_ite(expr* c, expr* t, expr* e, expr_ref& result) {
    bit_buffer t_bits;
    bit_buffer e_bits;
    get_bits(t, t_bits);
    get_bits(e, e_bits);
    SASSERT(t_bits.size() == e_bits.size());
    bit_buffer new_ites;
    unsigned num = t_bits.size();
    for (unsigned i = 0; i < num; ++i)
        new_ites.push_back(t_bits[i] == e_bits[i] ? t_bits[i] : m().mk_ite(c, t_bits[i], e_bits[i]));
    result = butil().mk_concat(new_ites.size(), new_ites.data());
}

void bv1_blaster_simplifier::rw_cfg::reduce_num(func_decl* f, expr_ref& result) {
    SASSERT(f->get_num_parameters() == 2);
    SASSERT(f->get_parameter(0).is_rational());
    SASSERT(f->get_parameter(1).is_int());
    bit_buffer bits;
    rational v  = f->get_parameter(0).get_rational();
    rational two(2);
    unsigned sz = f->get_parameter(1).get_int();
    for (unsigned i = 0; i < sz; ++i) {
        if ((v % two).is_zero())
            bits.push_back(m_bit0);
        else
            bits.push_back(m_bit1);
        v = div(v, two);
    }
    std::reverse(bits.begin(), bits.end());
    result = butil().mk_concat(bits.size(), bits.data());
}

void bv1_blaster_simplifier::rw_cfg::reduce_extract(func_decl* f, expr* arg, expr_ref& result) {
    bit_buffer arg_bits;
    get_bits(arg, arg_bits);
    SASSERT(arg_bits.size() == butil().get_bv_size(arg));
    unsigned high  = butil().get_extract_high(f);
    unsigned low   = butil().get_extract_low(f);
    unsigned sz    = arg_bits.size();
    unsigned start = sz - 1 - high;
    unsigned end   = sz - 1 - low;
    bit_buffer bits;
    for (unsigned i = start; i <= end; ++i)
        bits.push_back(arg_bits[i]);
    result = butil().mk_concat(bits.size(), bits.data());
}

void bv1_blaster_simplifier::rw_cfg::reduce_concat(unsigned num, expr* const* args, expr_ref& result) {
    bit_buffer bits;
    bit_buffer arg_bits;
    for (unsigned i = 0; i < num; ++i) {
        expr* arg = args[i];
        arg_bits.reset();
        get_bits(arg, arg_bits);
        bits.append(arg_bits.size(), arg_bits.data());
    }
    result = butil().mk_concat(bits.size(), bits.data());
}

void bv1_blaster_simplifier::rw_cfg::reduce_bin_xor(expr* arg1, expr* arg2, expr_ref& result) {
    bit_buffer bits1;
    bit_buffer bits2;
    get_bits(arg1, bits1);
    get_bits(arg2, bits2);
    SASSERT(bits1.size() == bits2.size());
    bit_buffer new_bits;
    unsigned num = bits1.size();
    for (unsigned i = 0; i < num; ++i)
        new_bits.push_back(m().mk_ite(m().mk_eq(bits1[i], bits2[i]), m_bit0, m_bit1));
    result = butil().mk_concat(new_bits.size(), new_bits.data());
}

void bv1_blaster_simplifier::rw_cfg::reduce_xor(unsigned num_args, expr* const* args, expr_ref& result) {
    SASSERT(num_args > 0);
    if (num_args == 1) {
        result = args[0];
        return;
    }
    reduce_bin_xor(args[0], args[1], result);
    for (unsigned i = 2; i < num_args; ++i)
        reduce_bin_xor(result, args[i], result);
}

br_status bv1_blaster_simplifier::rw_cfg::reduce_app(func_decl* f, unsigned num, expr* const* args,
                                                      expr_ref& result, proof_ref& result_pr) {
    result_pr = nullptr;
    if (num == 0 && f->get_family_id() == null_family_id && butil().is_bv_sort(f->get_range())) {
        mk_const(f, result);
        return BR_DONE;
    }

    if (m().is_eq(f)) {
        SASSERT(num == 2);
        if (butil().is_bv(args[0])) {
            reduce_eq(args[0], args[1], result);
            return BR_DONE;
        }
        return BR_FAILED;
    }

    if (m().is_ite(f)) {
        SASSERT(num == 3);
        if (butil().is_bv(args[1])) {
            reduce_ite(args[0], args[1], args[2], result);
            return BR_DONE;
        }
        return BR_FAILED;
    }

    if (f->get_family_id() == butil().get_family_id()) {
        switch (f->get_decl_kind()) {
        case OP_BV_NUM:
            reduce_num(f, result);
            return BR_DONE;
        case OP_EXTRACT:
            SASSERT(num == 1);
            reduce_extract(f, args[0], result);
            return BR_DONE;
        case OP_CONCAT:
            reduce_concat(num, args, result);
            return BR_DONE;
        case OP_BXOR:
            reduce_xor(num, args, result);
            return BR_DONE;
        default:
            return BR_FAILED;
        }
    }

    if (butil().is_bv_sort(f->get_range())) {
        blast_bv_term(m().mk_app(f, num, args), result);
        return BR_DONE;
    }

    return BR_FAILED;
}

void bv1_blaster_simplifier::collect_param_descrs(param_descrs& r) {
    insert_max_memory(r);
    insert_max_steps(r);
}

void bv1_blaster_simplifier::reduce() {
    auto& cfg = m_rw.cfg();
    unsigned prev_bits = cfg.m_newbits.size();

    expr_ref   new_curr(m);
    proof_ref  new_pr(m);

    for (unsigned idx : indices()) {
        auto const& d = m_fmls[idx];
        m_rw(d.fml(), new_curr, new_pr);
        if (d.fml() != new_curr)
            m_fmls.update(idx, dependent_expr(m, new_curr, mp(d.pr(), new_pr), d.dep()));
    }

    if (prev_bits == cfg.m_newbits.size())
        return;

    // Hide newly introduced bit variables in the model
    for (unsigned i = prev_bits; i < cfg.m_newbits.size(); ++i)
        m_fmls.model_trail().hide(cfg.m_newbits[i]);

    // Push definitions for constants whose bits were just introduced
    obj_hashtable<func_decl> new_bit_set;
    for (unsigned i = prev_bits; i < cfg.m_newbits.size(); ++i)
        new_bit_set.insert(cfg.m_newbits[i]);

    for (auto const& [f, v] : cfg.m_const2bits) {
        SASSERT(cfg.butil().is_concat(v));
        func_decl* first = to_app(to_app(v)->get_arg(0))->get_decl();
        if (new_bit_set.contains(first))
            m_fmls.model_trail().push(f, v, nullptr, {});
    }
}
