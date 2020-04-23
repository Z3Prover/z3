/*++
Copyright (c) 2006 Microsoft Corporation

Module Name:

    bv_decl_plugin.cpp

Abstract:

    <abstract>

Author:

    Leonardo de Moura (leonardo) 2008-01-09.

Revision History:

--*/
#include<sstream>
#include "ast/bv_decl_plugin.h"
#include "ast/arith_decl_plugin.h"
#include "util/warning.h"
#include "ast/ast_pp.h"
#include "ast/ast_smt2_pp.h"

bv_decl_plugin::bv_decl_plugin():
    m_bv_sym("bv"),
    m_concat_sym("concat"),
    m_sign_extend_sym("sign_extend"),
    m_zero_extend_sym("zero_extend"),
    m_extract_sym("extract"),
    m_rotate_left_sym("rotate_left"),
    m_rotate_right_sym("rotate_right"),
    m_repeat_sym("repeat"),
    m_bit2bool_sym("bit2bool"),
    m_mkbv_sym("mkbv"),
    m_bit0(nullptr),
    m_bit1(nullptr),
    m_carry(nullptr),
    m_xor3(nullptr),
    m_int_sort(nullptr) {
}

void bv_decl_plugin::set_manager(ast_manager * m, family_id id) {
    decl_plugin::set_manager(m, id);

    for (unsigned i = 1; i <= 64; i++) {
        mk_bv_sort(i);
    }
    m_bit0 = m->mk_const_decl(symbol("bit0"), get_bv_sort(1), func_decl_info(m_family_id, OP_BIT0));
    m_bit1 = m->mk_const_decl(symbol("bit1"), get_bv_sort(1), func_decl_info(m_family_id, OP_BIT1));
    m->inc_ref(m_bit0);
    m->inc_ref(m_bit1);

    sort * b = m->mk_bool_sort();
    sort * d[3] = {b, b, b};
    m_carry = m_manager->mk_func_decl(symbol("carry"), 3, d, b, func_decl_info(m_family_id, OP_CARRY));
    m_manager->inc_ref(m_carry);
    m_xor3 = m_manager->mk_func_decl(symbol("xor3"), 3, d, b, func_decl_info(m_family_id, OP_XOR3));
    m_manager->inc_ref(m_xor3);

    m_int_sort = m_manager->mk_sort(m_manager->mk_family_id("arith"), INT_SORT);
    SASSERT(m_int_sort != 0); // arith_decl_plugin must be installed before bv_decl_plugin.
    m_manager->inc_ref(m_int_sort);
}

void bv_decl_plugin::finalize() {
#define DEC_REF(FIELD) dec_range_ref(FIELD.begin(), FIELD.end(), *m_manager)
    if (m_bit0) { m_manager->dec_ref(m_bit0); }
    if (m_bit1) { m_manager->dec_ref(m_bit1); }
    if (m_carry) { m_manager->dec_ref(m_carry); }
    if (m_xor3) { m_manager->dec_ref(m_xor3); }
    if (m_int_sort) { m_manager->dec_ref(m_int_sort); }

    DEC_REF(m_bv_sorts);

    DEC_REF(m_bv_neg);
    DEC_REF(m_bv_add);
    DEC_REF(m_bv_sub);
    DEC_REF(m_bv_mul);

    DEC_REF(m_bv_sdiv);
    DEC_REF(m_bv_udiv);
    DEC_REF(m_bv_srem);
    DEC_REF(m_bv_urem);
    DEC_REF(m_bv_smod);

    DEC_REF(m_bv_sdiv0);
    DEC_REF(m_bv_udiv0);
    DEC_REF(m_bv_srem0);
    DEC_REF(m_bv_urem0);
    DEC_REF(m_bv_smod0);

    DEC_REF(m_bv_sdiv_i);
    DEC_REF(m_bv_udiv_i);
    DEC_REF(m_bv_srem_i);
    DEC_REF(m_bv_urem_i);
    DEC_REF(m_bv_smod_i);

    DEC_REF(m_bv_uleq);
    DEC_REF(m_bv_sleq);
    DEC_REF(m_bv_ugeq);
    DEC_REF(m_bv_sgeq);
    DEC_REF(m_bv_ult);
    DEC_REF(m_bv_slt);
    DEC_REF(m_bv_ugt);
    DEC_REF(m_bv_sgt);

    DEC_REF(m_bv_and);
    DEC_REF(m_bv_or);
    DEC_REF(m_bv_not);
    DEC_REF(m_bv_xor);
    DEC_REF(m_bv_nand);
    DEC_REF(m_bv_nor);
    DEC_REF(m_bv_xnor);

    DEC_REF(m_bv_redor);
    DEC_REF(m_bv_redand);
    DEC_REF(m_bv_comp);

    DEC_REF(m_bv_mul_ovfl);
    DEC_REF(m_bv_smul_ovfl);
    DEC_REF(m_bv_smul_udfl);

    DEC_REF(m_bv_shl);
    DEC_REF(m_bv_lshr);
    DEC_REF(m_bv_ashr);

    DEC_REF(m_ext_rotate_left);
    DEC_REF(m_ext_rotate_right);

    DEC_REF(m_int2bv);
    DEC_REF(m_bv2int);
    vector<ptr_vector<func_decl> >::iterator it  = m_bit2bool.begin();
    vector<ptr_vector<func_decl> >::iterator end = m_bit2bool.end();
    for (; it != end; ++it) {
        ptr_vector<func_decl> & ds = *it;
        DEC_REF(ds);
    }
    DEC_REF(m_mkbv);
}

void bv_decl_plugin::mk_bv_sort(unsigned bv_size) {
    force_ptr_array_size(m_bv_sorts, bv_size + 1);
    if (m_bv_sorts[bv_size] == 0) {
        parameter p(bv_size);
        sort_size sz;
        if (sort_size::is_very_big_base2(bv_size)) {
            sz = sort_size::mk_very_big();
        }
        else {
            sz = sort_size(rational::power_of_two(bv_size));
        }
        m_bv_sorts[bv_size] = m_manager->mk_sort(m_bv_sym, sort_info(m_family_id, BV_SORT, sz, 1, &p));
        m_manager->inc_ref(m_bv_sorts[bv_size]);
    }
}

inline sort * bv_decl_plugin::get_bv_sort(unsigned bv_size) {
    if (bv_size < (1 << 12)) {
        mk_bv_sort(bv_size);
            return m_bv_sorts[bv_size];
    }
    parameter p(bv_size);
    sort_size sz(sort_size::mk_very_big());
    return m_manager->mk_sort(m_bv_sym, sort_info(m_family_id, BV_SORT, sz, 1, &p));
}

sort * bv_decl_plugin::mk_sort(decl_kind k, unsigned num_parameters, parameter const * parameters) {
    if (!(num_parameters == 1 && parameters[0].is_int())) {
        m_manager->raise_exception("expecting one integer parameter to bit-vector sort");
    }
    unsigned bv_size = parameters[0].get_int();
    if (bv_size == 0) {
        m_manager->raise_exception("bit-vector size must be greater than zero");
    }
    mk_bv_sort(bv_size);
    return m_bv_sorts[bv_size];
}

func_decl * bv_decl_plugin::mk_binary(ptr_vector<func_decl> & decls, decl_kind k,
                                    char const * name, unsigned bv_size, bool ac, bool idempotent) {
    force_ptr_array_size(decls, bv_size + 1);

    if (decls[bv_size] == 0) {
        sort * s = get_bv_sort(bv_size);
        func_decl_info info(m_family_id, k);
        info.set_associative(ac);
        info.set_flat_associative(ac);
        info.set_commutative(ac);
        info.set_idempotent(idempotent);
        decls[bv_size] = m_manager->mk_func_decl(symbol(name), s, s, s, info);
        m_manager->inc_ref(decls[bv_size]);
    }

    return decls[bv_size];
}

func_decl * bv_decl_plugin::mk_unary(ptr_vector<func_decl> & decls, decl_kind k, char const * name, unsigned bv_size) {
    force_ptr_array_size(decls, bv_size + 1);

    if (decls[bv_size] == 0) {
        sort * s = get_bv_sort(bv_size);
        decls[bv_size] = m_manager->mk_func_decl(symbol(name), s, s, func_decl_info(m_family_id, k));
        m_manager->inc_ref(decls[bv_size]);
    }

    return decls[bv_size];
}

func_decl * bv_decl_plugin::mk_int2bv(unsigned bv_size, unsigned num_parameters, parameter const * parameters,
                                    unsigned arity, sort * const * domain) {
    if (bv_size == 0) {
        m_manager->raise_exception("bit-vector size must be greater than zero");
    }

    force_ptr_array_size(m_int2bv, bv_size + 1);

    if (arity != 1) {
        m_manager->raise_exception("expecting one argument to int2bv");
        return nullptr;
    }

    if (m_int2bv[bv_size] == 0) {
        sort * s = get_bv_sort(bv_size);
        m_int2bv[bv_size] = m_manager->mk_func_decl(symbol("int2bv"), domain[0], s,
                                                    func_decl_info(m_family_id, OP_INT2BV, num_parameters, parameters));
        m_manager->inc_ref(m_int2bv[bv_size]);
    }

    return m_int2bv[bv_size];
}

func_decl * bv_decl_plugin::mk_bv2int(unsigned bv_size, unsigned num_parameters, parameter const * parameters,
                                    unsigned arity, sort * const * domain) {
    force_ptr_array_size(m_bv2int, bv_size + 1);

    if (arity != 1) {
        m_manager->raise_exception("expecting one argument to bv2int");
        return nullptr;
    }

    if (m_bv2int[bv_size] == 0) {
        m_bv2int[bv_size] = m_manager->mk_func_decl(symbol("bv2int"), domain[0], m_int_sort,
                                                    func_decl_info(m_family_id, OP_BV2INT));
        m_manager->inc_ref(m_bv2int[bv_size]);
    }

    return m_bv2int[bv_size];
}

func_decl * bv_decl_plugin::mk_pred(ptr_vector<func_decl> & decls, decl_kind k, char const * name, unsigned bv_size) {
    force_ptr_array_size(decls, bv_size + 1);

    if (decls[bv_size] == 0) {
        sort * s = get_bv_sort(bv_size);
        decls[bv_size] = m_manager->mk_func_decl(symbol(name), s, s, m_manager->mk_bool_sort(), func_decl_info(m_family_id, k));
        m_manager->inc_ref(decls[bv_size]);
    }

    return decls[bv_size];
}

func_decl * bv_decl_plugin::mk_reduction(ptr_vector<func_decl> & decls, decl_kind k, char const * name, unsigned bv_size) {
    force_ptr_array_size(decls, bv_size + 1);

    if (decls[bv_size] == 0) {
        sort * d = get_bv_sort(bv_size);
        sort * r = get_bv_sort(1);
        decls[bv_size] = m_manager->mk_func_decl(symbol(name), d, r, func_decl_info(m_family_id, k));
        m_manager->inc_ref(decls[bv_size]);
    }

    return decls[bv_size];
}

func_decl * bv_decl_plugin::mk_comp(unsigned bv_size) {
    force_ptr_array_size(m_bv_comp, bv_size + 1);

    if (m_bv_comp[bv_size] == 0) {
        sort * d = get_bv_sort(bv_size);
        sort * r = get_bv_sort(1);
        func_decl_info info(m_family_id, OP_BCOMP);
        info.set_commutative();
        m_bv_comp[bv_size] = m_manager->mk_func_decl(symbol("bvcomp"), d, d, r, info);
        m_manager->inc_ref(m_bv_comp[bv_size]);
    }

    return m_bv_comp[bv_size];
}


func_decl * bv_decl_plugin::mk_func_decl(decl_kind k, unsigned bv_size) {
    switch (k) {
    case OP_BNEG:     return mk_unary(m_bv_neg, k, "bvneg", bv_size);
    case OP_BADD:     return mk_binary(m_bv_add, k, "bvadd", bv_size, true);
    case OP_BSUB:     return mk_binary(m_bv_sub, k, "bvsub", bv_size, false);
    case OP_BMUL:     return mk_binary(m_bv_mul, k, "bvmul", bv_size, true);
    case OP_BSDIV:    return mk_binary(m_bv_sdiv, k, "bvsdiv", bv_size, false);
    case OP_BUDIV:    return mk_binary(m_bv_udiv, k, "bvudiv", bv_size, false);
    case OP_BSREM:    return mk_binary(m_bv_srem, k, "bvsrem", bv_size, false);
    case OP_BUREM:    return mk_binary(m_bv_urem, k, "bvurem", bv_size, false);
    case OP_BSMOD:    return mk_binary(m_bv_smod, k, "bvsmod", bv_size, false);
    case OP_BSDIV0:   return mk_unary(m_bv_sdiv0, k, "bvsdiv0", bv_size);
    case OP_BUDIV0:   return mk_unary(m_bv_udiv0, k, "bvudiv0", bv_size);
    case OP_BSREM0:   return mk_unary(m_bv_srem0, k, "bvsrem0", bv_size);
    case OP_BUREM0:   return mk_unary(m_bv_urem0, k, "bvurem0", bv_size);
    case OP_BSMOD0:   return mk_unary(m_bv_smod0, k, "bvsmod0", bv_size);
    case OP_BSDIV_I:  return mk_binary(m_bv_sdiv_i, k, "bvsdiv_i", bv_size, false);
    case OP_BUDIV_I:  return mk_binary(m_bv_udiv_i, k, "bvudiv_i", bv_size, false);
    case OP_BSREM_I:  return mk_binary(m_bv_srem_i, k, "bvsrem_i", bv_size, false);
    case OP_BUREM_I:  return mk_binary(m_bv_urem_i, k, "bvurem_i", bv_size, false);
    case OP_BSMOD_I:  return mk_binary(m_bv_smod_i, k, "bvsmod_i", bv_size, false);
    case OP_ULEQ:     return mk_pred(m_bv_uleq, k, "bvule", bv_size);
    case OP_SLEQ:     return mk_pred(m_bv_sleq, k, "bvsle", bv_size);
    case OP_UGEQ:     return mk_pred(m_bv_ugeq, k, "bvuge", bv_size);
    case OP_SGEQ:     return mk_pred(m_bv_sgeq, k, "bvsge", bv_size);
    case OP_ULT:      return mk_pred(m_bv_ult, k, "bvult", bv_size);
    case OP_SLT:      return mk_pred(m_bv_slt, k, "bvslt", bv_size);
    case OP_UGT:      return mk_pred(m_bv_ugt, k, "bvugt", bv_size);
    case OP_SGT:      return mk_pred(m_bv_sgt, k, "bvsgt", bv_size);

    case OP_BAND:     return mk_binary(m_bv_and, k, "bvand", bv_size, true, true);
    case OP_BOR:      return mk_binary(m_bv_or, k, "bvor", bv_size, true, true);
    case OP_BNOT:     return mk_unary(m_bv_not, k, "bvnot", bv_size);
    case OP_BXOR:     return mk_binary(m_bv_xor, k, "bvxor", bv_size, true);
    case OP_BNAND:    return mk_binary(m_bv_nand, k, "bvnand", bv_size, false);
    case OP_BNOR:     return mk_binary(m_bv_nor, k, "bvnor", bv_size, false);
    case OP_BXNOR:    return mk_binary(m_bv_xnor, k, "bvxnor", bv_size, true);

    case OP_BREDOR:   return mk_reduction(m_bv_redor, k, "bvredor", bv_size);
    case OP_BREDAND:  return mk_reduction(m_bv_redand, k, "bvredand", bv_size);
    case OP_BCOMP:    return mk_comp(bv_size);
    case OP_BUMUL_NO_OVFL: return mk_pred(m_bv_mul_ovfl, k, "bvumul_noovfl", bv_size);
    case OP_BSMUL_NO_OVFL: return mk_pred(m_bv_smul_ovfl, k, "bvsmul_noovfl", bv_size);
    case OP_BSMUL_NO_UDFL: return mk_pred(m_bv_smul_udfl, k, "bvsmul_noudfl", bv_size);

    case OP_BSHL:     return mk_binary(m_bv_shl, k, "bvshl", bv_size, false);
    case OP_BLSHR:    return mk_binary(m_bv_lshr, k, "bvlshr", bv_size, false);
    case OP_BASHR:    return mk_binary(m_bv_ashr, k, "bvashr", bv_size, false);

    case OP_EXT_ROTATE_LEFT: return mk_binary(m_ext_rotate_left, k, "ext_rotate_left", bv_size, false);
    case OP_EXT_ROTATE_RIGHT: return mk_binary(m_ext_rotate_right, k, "ext_rotate_right", bv_size, false);
    default:          return nullptr;
    }
}

inline bool bv_decl_plugin::get_bv_size(sort * s, int & result) {
    if (s->get_family_id() == m_family_id && s->get_decl_kind() == BV_SORT) {
        result = s->get_parameter(0).get_int();
        return true;
    }
    return false;
}

inline bool bv_decl_plugin::get_bv_size(expr * t, int & result) {
    return get_bv_size(m_manager->get_sort(t), result);
}

bool bv_decl_plugin::get_concat_size(unsigned arity, sort * const * domain, int & result) {
    result = 0;
    for (unsigned i = 0; i < arity; i++) {
        int sz;
        if (!get_bv_size(domain[i], sz)) {
            return false;
        }
        result += sz;
    }
    return true;
}

bool bv_decl_plugin::get_extend_size(unsigned num_parameters, parameter const * parameters,
    unsigned arity, sort * const * domain, int & result) {
    int arg_sz;
    if (arity != 1 || !get_bv_size(domain[0], arg_sz) ||
        num_parameters != 1 || !parameters[0].is_int() || parameters[0].get_int() < 0) {
        return false;
    }
    result = arg_sz + parameters[0].get_int();
    return true;
}

bool bv_decl_plugin::get_extract_size(unsigned num_parameters, parameter const * parameters,
                                    unsigned arity, sort * const * domain, int & result) {
    int arg_sz;
    if (arity != 1 ||
        !get_bv_size(domain[0], arg_sz) ||
        num_parameters != 2 ||
        !parameters[0].is_int() ||
        !parameters[1].is_int() ||
        parameters[1].get_int() > parameters[0].get_int() ||
        parameters[0].get_int() >= arg_sz) {
        return false;
    }
    result = parameters[0].get_int() - parameters[1].get_int() + 1;
    return true;
}

bool bv_decl_plugin::get_int2bv_size(unsigned num_parameters, parameter const * parameters, int & result) {
    if (num_parameters != 1) {
        m_manager->raise_exception("int2bv expects one parameter");
        return false;
    }
    const parameter &p = parameters[0];
    if (p.is_int()) {
        result = p.get_int();
        return true;
    }
    if (!p.is_ast() || !is_expr(p.get_ast())) {
        m_manager->raise_exception("int2bv expects one integer parameter");
        return false;
    }
    return get_bv_size(to_expr(p.get_ast()), result);
}


func_decl * bv_decl_plugin::mk_num_decl(unsigned num_parameters, parameter const * parameters, unsigned arity) {
    if (!(num_parameters == 2 && arity == 0 && parameters[0].is_rational() && parameters[1].is_int())) {
        m_manager->raise_exception("invalid bit-vector numeral declaration");
        return nullptr;
    }
    unsigned bv_size = parameters[1].get_int();
    if (bv_size == 0) {
        m_manager->raise_exception("bit-vector size must be greater than zero");
    }
    // TODO: sign an error if the parameters[0] is out of range, that is, it is a value not in [0, 2^{bv_size})
    // This cannot be enforced now, since some Z3 modules try to generate these invalid numerals.
    // After SMT-COMP, I should find all offending modules.
    // For now, I will just simplify the numeral here.
    parameter p0(mod(parameters[0].get_rational(), rational::power_of_two(bv_size)));
    parameter ps[2] = { std::move(p0), parameters[1] };
    sort * bv = get_bv_sort(bv_size);
    return m_manager->mk_const_decl(m_bv_sym, bv, func_decl_info(m_family_id, OP_BV_NUM, num_parameters, ps));
}

func_decl * bv_decl_plugin::mk_bit2bool(unsigned bv_size, unsigned num_parameters, parameter const * parameters,
                                        unsigned arity, sort * const * domain) {
    if (!(num_parameters == 1 && parameters[0].is_int() && arity == 1 && parameters[0].get_int() < static_cast<int>(bv_size))) {
        m_manager->raise_exception("invalid bit2bool declaration");
        return nullptr;
    }
    unsigned idx = parameters[0].get_int();
    m_bit2bool.reserve(bv_size+1);
    ptr_vector<func_decl> & v = m_bit2bool[bv_size];
    v.reserve(bv_size, 0);
    if (v[idx] == 0) {
        v[idx] = m_manager->mk_func_decl(m_bit2bool_sym, domain[0], m_manager->mk_bool_sort(),
                                         func_decl_info(m_family_id, OP_BIT2BOOL, num_parameters, parameters));
        m_manager->inc_ref(v[idx]);
    }
    return v[idx];
}

func_decl * bv_decl_plugin::mk_mkbv(unsigned arity, sort * const * domain) {
    for (unsigned i = 0; i < arity; i++) {
        if (!m_manager->is_bool(domain[i])) {
            m_manager->raise_exception("invalid mkbv operator");
            return nullptr;
        }
    }
    unsigned bv_size = arity;
    m_mkbv.reserve(bv_size+1);
    if (m_mkbv[bv_size] == 0) {
        m_mkbv[bv_size] = m_manager->mk_func_decl(m_mkbv_sym, arity, domain, get_bv_sort(bv_size), func_decl_info(m_family_id, OP_MKBV));
        m_manager->inc_ref(m_mkbv[bv_size]);
    }
    return m_mkbv[bv_size];
}

func_decl * bv_decl_plugin::mk_func_decl(decl_kind k, unsigned num_parameters, parameter const * parameters,
                                         unsigned arity, sort * const * domain, sort * range) {
    int bv_size;
    if (k == OP_INT2BV && get_int2bv_size(num_parameters, parameters, bv_size)) {
        // bv_size is filled in.
    }
    else if (k == OP_BV_NUM) {
        return mk_num_decl(num_parameters, parameters, arity);
    }
    else if (k == OP_BIT0) {
        return m_bit0;
    }
    else if (k == OP_BIT1) {
        return m_bit1;
    }
    else if (k == OP_CARRY) {
        return m_carry;
    }
    else if (k == OP_XOR3) {
        return m_xor3;
    }
    else if (k == OP_MKBV) {
        return mk_mkbv(arity, domain);
    }
    else if (arity == 0) {
        m_manager->raise_exception("no arguments supplied to bit-vector operator");
        return nullptr;
    }
    else if (!get_bv_size(domain[0], bv_size)) {
        m_manager->raise_exception("could not extract bit-vector size");
        return nullptr;
    }
    func_decl * r = mk_func_decl(k, bv_size);
    if (r != nullptr) {
        if (arity != r->get_arity()) {
            if (r->get_info()->is_associative())
                arity = r->get_arity();
            else {
                m_manager->raise_exception("declared arity mismatches supplied arity");
                return nullptr;
            }
        }
        for (unsigned i = 0; i < arity; ++i) {
            if (domain[i] != r->get_domain(i)) {
                m_manager->raise_exception("declared sorts do not match supplied sorts");
                return nullptr;
            }
        }
        return r;
    }
    int r_size;
    switch (k) {
    case OP_BIT2BOOL:
        return mk_bit2bool(bv_size, num_parameters, parameters, arity, domain);
    case OP_INT2BV:
        return mk_int2bv(bv_size, num_parameters, parameters, arity, domain);
    case OP_BV2INT:
        return mk_bv2int(bv_size, num_parameters, parameters, arity, domain);
    case OP_CONCAT:
        if (!get_concat_size(arity, domain, r_size))
            m_manager->raise_exception("invalid concat application");
        return m_manager->mk_func_decl(m_concat_sym, arity, domain, get_bv_sort(r_size),
                                       func_decl_info(m_family_id, k));
    case OP_SIGN_EXT:
        if (!get_extend_size(num_parameters, parameters, arity, domain, r_size))
            m_manager->raise_exception("invalid sign_extend application");
        return m_manager->mk_func_decl(m_sign_extend_sym, arity, domain, get_bv_sort(r_size),
                                       func_decl_info(m_family_id, k, num_parameters, parameters));
    case OP_ZERO_EXT:
        if (!get_extend_size(num_parameters, parameters, arity, domain, r_size))
            m_manager->raise_exception("invalid zero_extend application");
        return m_manager->mk_func_decl(m_zero_extend_sym, arity, domain, get_bv_sort(r_size),
                                       func_decl_info(m_family_id, k, num_parameters, parameters));
    case OP_EXTRACT:
        if (!get_extract_size(num_parameters, parameters, arity, domain, r_size))
            m_manager->raise_exception("invalid extract application");
        return m_manager->mk_func_decl(m_extract_sym, arity, domain, get_bv_sort(r_size),
                                       func_decl_info(m_family_id, k, num_parameters, parameters));
    case OP_ROTATE_LEFT:
        if (arity != 1)
            m_manager->raise_exception("rotate left expects one argument");
        if (num_parameters != 1 || !parameters[0].is_int()) 
            m_manager->raise_exception("rotate left expects one integer parameter");
        return m_manager->mk_func_decl(m_rotate_left_sym, arity, domain, domain[0],
                                       func_decl_info(m_family_id, k, num_parameters, parameters));
    case OP_ROTATE_RIGHT:
        if (arity != 1)
            m_manager->raise_exception("rotate right expects one argument");
        if (num_parameters != 1 || !parameters[0].is_int()) 
            m_manager->raise_exception("rotate right expects one integer parameter");
        return m_manager->mk_func_decl(m_rotate_right_sym, arity, domain, domain[0],
                                       func_decl_info(m_family_id, k, num_parameters, parameters));
    case OP_REPEAT:
        if (arity != 1)
            m_manager->raise_exception("repeat expects one argument");
        if (num_parameters != 1 || !parameters[0].is_int() || parameters[0].get_int() == 0)
            m_manager->raise_exception("repeat expects one nonzero integer parameter");
        if (!get_bv_size(domain[0], bv_size))
            m_manager->raise_exception("repeat expects an argument with bit-vector sort");
        return m_manager->mk_func_decl(m_repeat_sym, arity, domain, get_bv_sort(bv_size * parameters[0].get_int()),
                                       func_decl_info(m_family_id, k, num_parameters, parameters));
    default:
        return nullptr;
    }
}

func_decl * bv_decl_plugin::mk_func_decl(decl_kind k, unsigned num_parameters, parameter const * parameters,
                                         unsigned num_args, expr * const * args, sort * range) {
    ast_manager& m = *m_manager;
    int bv_size;
    if (k == OP_INT2BV && get_int2bv_size(num_parameters, parameters, bv_size)) {
        // bv_size is filled in.
    }
    else if (k == OP_BV_NUM) {
        return mk_num_decl(num_parameters, parameters, num_args);
    }
    else if (k == OP_BIT0) {
        return m_bit0;
    }
    else if (k == OP_BIT1) {
        return m_bit1;
    }
    else if (k == OP_CARRY) {
        return m_carry;
    }
    else if (k == OP_XOR3) {
        return m_xor3;
    }
    else if (k == OP_MKBV) {
        return decl_plugin::mk_func_decl(k, num_parameters, parameters, num_args, args, range);
    }
    else if (num_args == 0 || !get_bv_size(args[0], bv_size)) {
        m.raise_exception("operator is applied to arguments of the wrong sort");
        return nullptr;
    }
    func_decl * r = mk_func_decl(k, bv_size);
    if (r != nullptr) {
        if (num_args != r->get_arity()) {
            if (r->get_info()->is_associative()) {
                sort * fs = r->get_domain(0);
                for (unsigned i = 0; i < num_args; ++i) {
                    if (m.get_sort(args[i]) != fs) {
                        m_manager->raise_exception("declared sorts do not match supplied sorts");
                        return nullptr;
                    }
                }
                return r;
            }
            else {
                m.raise_exception("declared arity mismatches supplied arity");
                return nullptr;
            }
        }
        for (unsigned i = 0; i < num_args; ++i) {
            if (m.get_sort(args[i]) != r->get_domain(i)) {
                std::ostringstream buffer;
                buffer << "Argument " << mk_pp(args[i], m) << " at position " << i << " does not match declaration " << mk_pp(r, m);
                m.raise_exception(buffer.str());
                return nullptr;
            }
        }
        return r;
    }
    return decl_plugin::mk_func_decl(k, num_parameters, parameters, num_args, args, range);
}

bool bv_decl_plugin::is_value(app* e) const {
    return is_app_of(e, m_family_id, OP_BV_NUM);
}

void bv_decl_plugin::get_offset_term(app * a, expr * & t, rational & offset) const {
    family_id fid = get_family_id();
    if (a->get_num_args() == 2 && is_app_of(a, fid, OP_BADD) && is_app_of(a->get_arg(0), fid, OP_BV_NUM)) {
        unsigned sz;
        func_decl * decl = to_app(a->get_arg(0))->get_decl();
        offset = decl->get_parameter(0).get_rational();
        sz     = decl->get_parameter(1).get_int();
        t      = a->get_arg(1);
        offset = mod(offset, rational::power_of_two(sz));
    }
    else {
        t      = a;
        offset = rational(0);
    }
}

bool bv_decl_plugin::are_distinct(app * a, app * b) const {
#if 1
    // Check for a + k1 != a + k2   when k1 != k2
    rational a_offset;
    expr *   a_term;
    rational b_offset;
    expr *   b_term;
    get_offset_term(a, a_term, a_offset);
    get_offset_term(b, b_term, b_offset);
    TRACE("bv_are_distinct",
          tout << mk_ismt2_pp(a, *m_manager) << "\n" << mk_ismt2_pp(b, *m_manager) << "\n";
          tout << "---->\n";
          tout << "a: " << a_offset << " + " << mk_ismt2_pp(a_term, *m_manager) << "\n";
          tout << "b: " << b_offset << " + " << mk_ismt2_pp(b_term, *m_manager) << "\n";);
    if (a_term == b_term && a_offset != b_offset)
        return true;
#endif
    return decl_plugin::are_distinct(a, b);
}

void bv_decl_plugin::get_sort_names(svector<builtin_name> & sort_names, symbol const & logic) {
    if (logic == symbol::null || logic == symbol("ALL"))
        sort_names.push_back(builtin_name("bv", BV_SORT));
    sort_names.push_back(builtin_name("BitVec", BV_SORT));
}

void bv_decl_plugin::get_op_names(svector<builtin_name> & op_names, symbol const & logic) {
    op_names.push_back(builtin_name("bit1",OP_BIT1));
    op_names.push_back(builtin_name("bit0",OP_BIT0));
    op_names.push_back(builtin_name("bvneg",OP_BNEG));
    op_names.push_back(builtin_name("bvadd",OP_BADD));
    op_names.push_back(builtin_name("bvsub",OP_BSUB));
    op_names.push_back(builtin_name("bvmul",OP_BMUL));
    op_names.push_back(builtin_name("bvsdiv",OP_BSDIV));
    op_names.push_back(builtin_name("bvudiv",OP_BUDIV));
    op_names.push_back(builtin_name("bvsrem",OP_BSREM));
    op_names.push_back(builtin_name("bvurem",OP_BUREM));
    op_names.push_back(builtin_name("bvsmod",OP_BSMOD));

    op_names.push_back(builtin_name("bvule",OP_ULEQ));
    op_names.push_back(builtin_name("bvsle",OP_SLEQ));
    op_names.push_back(builtin_name("bvuge",OP_UGEQ));
    op_names.push_back(builtin_name("bvsge",OP_SGEQ));
    op_names.push_back(builtin_name("bvult",OP_ULT));
    op_names.push_back(builtin_name("bvslt",OP_SLT));
    op_names.push_back(builtin_name("bvugt",OP_UGT));
    op_names.push_back(builtin_name("bvsgt",OP_SGT));
    op_names.push_back(builtin_name("bvand",OP_BAND));
    op_names.push_back(builtin_name("bvor",OP_BOR));
    op_names.push_back(builtin_name("bvnot",OP_BNOT));
    op_names.push_back(builtin_name("bvxor",OP_BXOR));
    op_names.push_back(builtin_name("bvnand",OP_BNAND));
    op_names.push_back(builtin_name("bvnor",OP_BNOR));
    op_names.push_back(builtin_name("bvxnor",OP_BXNOR));
    op_names.push_back(builtin_name("concat",OP_CONCAT));
    op_names.push_back(builtin_name("sign_extend",OP_SIGN_EXT));
    op_names.push_back(builtin_name("zero_extend",OP_ZERO_EXT));
    op_names.push_back(builtin_name("extract",OP_EXTRACT));
    op_names.push_back(builtin_name("repeat",OP_REPEAT));
    op_names.push_back(builtin_name("bvredor",OP_BREDOR));
    op_names.push_back(builtin_name("bvredand",OP_BREDAND));
    op_names.push_back(builtin_name("bvcomp",OP_BCOMP));
    op_names.push_back(builtin_name("bvshl",OP_BSHL));
    op_names.push_back(builtin_name("bvlshr",OP_BLSHR));
    op_names.push_back(builtin_name("bvashr",OP_BASHR));
    op_names.push_back(builtin_name("rotate_left",OP_ROTATE_LEFT));
    op_names.push_back(builtin_name("rotate_right",OP_ROTATE_RIGHT));
    op_names.push_back(builtin_name("bit2bool", OP_BIT2BOOL));

    if (logic == symbol::null || logic == symbol("ALL") || logic == "QF_FD") {
        op_names.push_back(builtin_name("bvumul_noovfl",OP_BUMUL_NO_OVFL));
        op_names.push_back(builtin_name("bvsmul_noovfl",OP_BSMUL_NO_OVFL));
        op_names.push_back(builtin_name("bvsmul_noudfl",OP_BSMUL_NO_UDFL));

        op_names.push_back(builtin_name("bvsdiv0", OP_BSDIV0));
        op_names.push_back(builtin_name("bvudiv0", OP_BUDIV0));
        op_names.push_back(builtin_name("bvsrem0", OP_BSREM0));
        op_names.push_back(builtin_name("bvurem0", OP_BUREM0));
        op_names.push_back(builtin_name("bvsmod0", OP_BSMOD0));

        op_names.push_back(builtin_name("bvsdiv_i", OP_BSDIV_I));
        op_names.push_back(builtin_name("bvudiv_i", OP_BUDIV_I));
        op_names.push_back(builtin_name("bvsrem_i", OP_BSREM_I));
        op_names.push_back(builtin_name("bvurem_i", OP_BUREM_I));
        op_names.push_back(builtin_name("bvsmod_i", OP_BSMOD_I));

        op_names.push_back(builtin_name("ext_rotate_left",OP_EXT_ROTATE_LEFT));
        op_names.push_back(builtin_name("ext_rotate_right",OP_EXT_ROTATE_RIGHT));
        op_names.push_back(builtin_name("int2bv",OP_INT2BV));
        op_names.push_back(builtin_name("bv2int",OP_BV2INT));
        op_names.push_back(builtin_name("bv2nat",OP_BV2INT));
        op_names.push_back(builtin_name("mkbv",OP_MKBV));
    }
}

expr * bv_decl_plugin::get_some_value(sort * s) {
    SASSERT(s->is_sort_of(m_family_id, BV_SORT));
    unsigned bv_size = s->get_parameter(0).get_int();
    parameter p[2] = { parameter(rational::zero()), parameter(static_cast<int>(bv_size)) };
    return m_manager->mk_app(m_family_id, OP_BV_NUM, 2, p, 0, nullptr);
}

rational bv_recognizers::norm(rational const & val, unsigned bv_size, bool is_signed) const {
    rational r = mod(val, rational::power_of_two(bv_size));
    SASSERT(!r.is_neg());
    if (is_signed) {
        if (r >= rational::power_of_two(bv_size - 1)) {
            r -= rational::power_of_two(bv_size);
        }
        if (r < -rational::power_of_two(bv_size - 1)) {
            r += rational::power_of_two(bv_size);
        }
    }
    return r;
}

bool bv_recognizers::has_sign_bit(rational const & n, unsigned bv_size) const {
    SASSERT(bv_size > 0);
    rational m = norm(n, bv_size, false);
    rational p = rational::power_of_two(bv_size - 1);
    return m >= p;
}

bool bv_recognizers::is_bv_sort(sort const * s) const {
    return (s->get_family_id() == get_fid() && s->get_decl_kind() == BV_SORT && s->get_num_parameters() == 1);
}

bool bv_recognizers::is_numeral(expr const * n, rational & val, unsigned & bv_size) const {
    if (!is_app_of(n, get_fid(), OP_BV_NUM)) {
        return false;
    }
    func_decl * decl = to_app(n)->get_decl();
    val     = decl->get_parameter(0).get_rational();
    bv_size = decl->get_parameter(1).get_int();
    return true;
}

bool bv_recognizers::is_numeral(expr const * n, rational & val) const {
    unsigned bv_size = 0;
    return is_numeral(n, val, bv_size);
}


bool bv_recognizers::is_allone(expr const * e) const {
    rational r;
    unsigned bv_size;
    if (!is_numeral(e, r, bv_size)) {
        return false;
    }
    bool result = (r == rational::power_of_two(bv_size) - rational(1));
    TRACE("is_allone", tout << r << " " << result << "\n";);
    return result;
}

bool bv_recognizers::is_zero(expr const * n) const {
    if (!is_app_of(n, get_fid(), OP_BV_NUM)) {
        return false;
    }
    func_decl * decl = to_app(n)->get_decl();
    return decl->get_parameter(0).get_rational().is_zero();
}

bool bv_recognizers::is_extract(expr const* e, unsigned& low, unsigned& high, expr*& b) const {
    if (!is_extract(e)) return false;
    low = get_extract_low(e);
    high = get_extract_high(e);
    b = to_app(e)->get_arg(0);
    return true;
}

bool bv_recognizers::is_bv2int(expr const* e, expr*& r) const {
    if (!is_bv2int(e)) return false;
    r = to_app(e)->get_arg(0);
    return true;
}

bool bv_recognizers::mult_inverse(rational const & n, unsigned bv_size, rational & result) {
    if (n.is_one()) {
        result = n;
        return true;
    }

    if (!mod(n, rational(2)).is_one()) {
        return false;
    }

    rational g;
    rational x;
    rational y;
    g = gcd(n, rational::power_of_two(bv_size), x, y);
    if (x.is_neg()) {
        x = mod(x, rational::power_of_two(bv_size));
    }
    SASSERT(x.is_pos());
    SASSERT(mod(x * n, rational::power_of_two(bv_size)).is_one());
    result = x;
    return true;
}

bv_util::bv_util(ast_manager & m):
    bv_recognizers(m.mk_family_id(symbol("bv"))),
    m_manager(m) {
    m_plugin = static_cast<bv_decl_plugin*>(m.get_plugin(m.mk_family_id("bv")));
    SASSERT(m.has_plugin(symbol("bv")));
    }

app * bv_util::mk_numeral(rational const & val, sort* s) const {
    if (!is_bv_sort(s)) {
        return nullptr;
    }
    unsigned bv_size = get_bv_size(s);
    return mk_numeral(val, bv_size);
}

app * bv_util::mk_numeral(rational const & val, unsigned bv_size) const {
    parameter p[2] = { parameter(val), parameter(static_cast<int>(bv_size)) };
    app * r = m_manager.mk_app(get_fid(), OP_BV_NUM, 2, p, 0, nullptr);

    if (m_plugin->log_constant_meaning_prelude(r)) {
        if (bv_size % 4 == 0) {
            m_manager.trace_stream() << "#x";
            val.display_hex(m_manager.trace_stream(), bv_size);
            m_manager.trace_stream() << "\n";
        } else {
            m_manager.trace_stream() << "#b";
            val.display_bin(m_manager.trace_stream(), bv_size);
            m_manager.trace_stream() << "\n";
        }
    }

    return r;
}

sort * bv_util::mk_sort(unsigned bv_size) {
    parameter p[1] = { parameter(bv_size) };
    return m_manager.mk_sort(get_fid(), BV_SORT, 1, p);
}

unsigned bv_util::get_int2bv_size(parameter const& p) {
    int sz;
    VERIFY(m_plugin->get_int2bv_size(1, &p, sz));
    return static_cast<unsigned>(sz);
}

app * bv_util::mk_bv2int(expr* e) {
    sort* s = m_manager.mk_sort(m_manager.mk_family_id("arith"), INT_SORT);
    parameter p(s);
    return m_manager.mk_app(get_fid(), OP_BV2INT, 1, &p, 1, &e);
}
