/*++
Copyright (c) 2013 Microsoft Corporation

Module Name:

    pb_decl_plugin.cpp

Abstract:

    Cardinality Constraints plugin

Author:

    Nikolaj Bjorner (nbjorner) 2013-05-11

Revision History:

--*/

#include "ast/pb_decl_plugin.h"
#include "ast/ast_util.h"
#include "ast/ast_pp.h"

pb_decl_plugin::pb_decl_plugin():
    m_at_most_sym("at-most"),
    m_at_least_sym("at-least"),
    m_pble_sym("pble"),
    m_pbge_sym("pbge"),
    m_pbeq_sym("pbeq")
{}

func_decl * pb_decl_plugin::mk_func_decl(decl_kind k, unsigned num_parameters, parameter const * parameters, 
                                         unsigned arity, sort * const * domain, sort * range) {
    SASSERT(m_manager);
    ast_manager& m = *m_manager;
    for (unsigned i = 0; i < arity; ++i) {
        if (!m.is_bool(domain[i])) {
            m.raise_exception("invalid non-Boolean sort applied to 'at-most'");
        }
    }
    symbol sym;
    switch(k) {
    case OP_AT_LEAST_K: sym = m_at_least_sym; break;
    case OP_AT_MOST_K: sym = m_at_most_sym; break;
    case OP_PB_LE: sym = m_pble_sym; break;
    case OP_PB_GE: sym = m_pbge_sym; break;
    case OP_PB_EQ: sym = m_pbeq_sym; break;
    default: break;
    }
    switch(k) {
    case OP_AT_LEAST_K:
    case OP_AT_MOST_K: {
        if (num_parameters != 1 || !parameters[0].is_int() || parameters[0].get_int() < 0) {
            m.raise_exception("function expects one non-negative integer parameter");
        }
        func_decl_info info(m_family_id, k, 1, parameters);
        return m.mk_func_decl(sym, arity, domain, m.mk_bool_sort(), info);
    }      
    case OP_PB_GE:
    case OP_PB_LE: 
    case OP_PB_EQ: {
        if (num_parameters != 1 + arity) {
            m.raise_exception("function expects arity+1 rational parameters");
        }
        vector<parameter> params;
        for (unsigned i = 0; i < num_parameters; ++i) {
            parameter const& p = parameters[i];
            if (p.is_int()) {
                params.push_back(p);
            }
            else if (p.is_rational()) {
                // HACK: ast pretty printer does not work with rationals.
                rational const& r = p.get_rational();
                if (r.is_int32()) {
                    params.push_back(parameter(r.get_int32()));
                }
                else {
                    params.push_back(p);
                }
            }
            else {
                m.raise_exception("functions 'pble/pbge/pbeq' expect arity+1 integer parameters");
            }
        }
        func_decl_info info(m_family_id, k, num_parameters, params.c_ptr());
        return m.mk_func_decl(sym, arity, domain, m.mk_bool_sort(), info);
    }
    default:
        UNREACHABLE();
        return nullptr;
    }
}

void pb_decl_plugin::get_op_names(svector<builtin_name> & op_names, symbol const & logic) {
    if (logic == symbol::null || logic == "QF_FD" || logic == "ALL" || logic == "HORN") {
        op_names.push_back(builtin_name(m_at_most_sym.bare_str(), OP_AT_MOST_K));
        op_names.push_back(builtin_name(m_at_least_sym.bare_str(), OP_AT_LEAST_K));
        op_names.push_back(builtin_name(m_pble_sym.bare_str(), OP_PB_LE));
        op_names.push_back(builtin_name(m_pbge_sym.bare_str(), OP_PB_GE));
        op_names.push_back(builtin_name(m_pbeq_sym.bare_str(), OP_PB_EQ));
    }
}

void pb_util::normalize(unsigned num_args, rational const* coeffs, rational const& k) {
    m_coeffs.reset();
    bool all_ones = true;
    for (unsigned i = 0; i < num_args && all_ones; ++i) {
        all_ones = denominator(coeffs[i]).is_one();
    }
    if (all_ones) {
        for (unsigned i = 0; i < num_args; ++i) {
            m_coeffs.push_back(coeffs[i]);
        }
        m_k = k;        
    }
    else {
        rational d(1);
        for (unsigned i = 0; i < num_args; ++i) {
            d = lcm(d, denominator(coeffs[i]));
        }
        for (unsigned i = 0; i < num_args; ++i) {
            m_coeffs.push_back(d*coeffs[i]);
        }
        m_k = d*k;
    }
}

app * pb_util::mk_le(unsigned num_args, rational const * coeffs, expr * const * args, rational const& k) {
    normalize(num_args, coeffs, k);
    m_params.reset();
    m_params.push_back(parameter(floor(m_k)));
    bool all_ones = true;
    for (unsigned i = 0; i < num_args; ++i) {
        all_ones &= m_coeffs[i].is_one();
        m_params.push_back(parameter(m_coeffs[i]));
    }
    if (all_ones && k.is_unsigned() && floor(m_k).is_int32()) {
        m_params[0] = parameter(floor(m_k).get_int32());
        return m.mk_app(m_fid, OP_AT_MOST_K, 1, m_params.c_ptr(), num_args, args, m.mk_bool_sort());
    }
    return m.mk_app(m_fid, OP_PB_LE, m_params.size(), m_params.c_ptr(), num_args, args, m.mk_bool_sort());
}

app * pb_util::mk_ge(unsigned num_args, rational const * coeffs, expr * const * args, rational const& k) {
    normalize(num_args, coeffs, k);
    m_params.reset();
    m_params.push_back(parameter(ceil(m_k)));
    bool all_ones = true;
    for (unsigned i = 0; i < num_args; ++i) {
        all_ones &= m_coeffs[i].is_one();
        m_params.push_back(parameter(m_coeffs[i]));
    }
    if (all_ones && k.is_unsigned()) {
        m_params[0] = parameter(ceil(m_k).get_unsigned());
        return m.mk_app(m_fid, OP_AT_LEAST_K, 1, m_params.c_ptr(), num_args, args, m.mk_bool_sort());
    }
    return m.mk_app(m_fid, OP_PB_GE, m_params.size(), m_params.c_ptr(), num_args, args, m.mk_bool_sort());
}

app * pb_util::mk_eq(unsigned num_args, rational const * coeffs, expr * const * args, rational const& k) {
    normalize(num_args, coeffs, k);
    if (!m_k.is_int()) {
        return m.mk_false();
    }
    if (num_args == 0) {
        return m_k.is_zero() ? m.mk_true() : m.mk_false();
    }
    m_params.reset();
    m_params.push_back(parameter(m_k));
    for (unsigned i = 0; i < num_args; ++i) {
        m_params.push_back(parameter(m_coeffs[i]));
    }
    return m.mk_app(m_fid, OP_PB_EQ, m_params.size(), m_params.c_ptr(), num_args, args, m.mk_bool_sort());
}

// ax + by < k
// <=>
// -ax - by >= -k + 1
// <=>
// a(1-x) + b(1-y) >= -k + a + b + 1
app * pb_util::mk_lt(unsigned num_args, rational const * _coeffs, expr * const * _args, rational const& _k) {
    normalize(num_args, _coeffs, _k);
    expr_ref_vector args(m);
    for (unsigned i = 0; i < num_args; ++i) {
        args.push_back(mk_not(m, _args[i]));
    }
    m_k = floor(m_k);
    m_k.neg();
    m_k += rational::one();
    for (unsigned i = 0; i < num_args; ++i) {
        m_k += m_coeffs[i];
    }
    return mk_ge(num_args, m_coeffs.c_ptr(), args.c_ptr(), m_k);
}


app * pb_util::mk_at_most_k(unsigned num_args, expr * const * args, unsigned k) {
    parameter param(k);
    return m.mk_app(m_fid, OP_AT_MOST_K, 1, &param, num_args, args, m.mk_bool_sort());
}

bool pb_util::is_at_most_k(func_decl *a) const {
    return is_decl_of(a, m_fid, OP_AT_MOST_K);
}

bool pb_util::is_at_most_k(expr *a, rational& k) const {
    if (is_at_most_k(a)) {
        k = get_k(a);
        return true;
    }
    else {
        return false;
    }
}

app * pb_util::mk_at_least_k(unsigned num_args, expr * const * args, unsigned k) {
    parameter param(k);
    return m.mk_app(m_fid, OP_AT_LEAST_K, 1, &param, num_args, args, m.mk_bool_sort());
}

bool pb_util::is_at_least_k(func_decl *a) const {
    return is_decl_of(a, m_fid, OP_AT_LEAST_K);
}

bool pb_util::is_at_least_k(expr *a, rational& k) const {
    if (is_at_least_k(a)) {
        k = get_k(a);
        return true;
    }
    else {
        return false;
    }
}

rational pb_util::get_k(func_decl *a) const {
    parameter const& p = a->get_parameter(0);
    if (is_at_most_k(a) || is_at_least_k(a)) {
        return to_rational(p);
    }
    else {
        SASSERT(is_le(a) || is_ge(a) || is_eq(a));
        return to_rational(p);
    }
}


bool pb_util::is_le(func_decl *a) const {
    return is_decl_of(a, m_fid, OP_PB_LE);
}

bool pb_util::is_le(expr* a, rational& k) const {
    if (is_le(a)) {
        k = get_k(a);
        return true;
    }
    else {
        return false;
    }
}

bool pb_util::is_ge(func_decl *a) const {
    return is_decl_of(a, m_fid, OP_PB_GE);
}

bool pb_util::is_ge(expr* a, rational& k) const {
    if (is_ge(a)) {
        k = get_k(a);
        return true;
    }
    else {
        return false;
    }
}


bool pb_util::is_eq(func_decl *a) const {
    return is_decl_of(a, m_fid, OP_PB_EQ);
}

bool pb_util::is_eq(expr* a, rational& k) const {
    if (is_eq(a)) {
        k = get_k(a);
        return true;
    }
    else {
        return false;
    }
}

rational pb_util::get_coeff(func_decl* a, unsigned index) const {
    if (is_at_most_k(a) || is_at_least_k(a)) {
        return rational::one();
    }
    SASSERT(is_le(a) || is_ge(a) || is_eq(a));
    SASSERT(1 + index < a->get_num_parameters());
    return to_rational(a->get_parameter(index + 1));
}

rational pb_util::to_rational(parameter const& p) const {
    if (p.is_int()) {
        return rational(p.get_int());
    }
    SASSERT(p.is_rational());
    return p.get_rational();
}

bool pb_util::has_unit_coefficients(func_decl* f) const {
    if (is_at_most_k(f) || is_at_least_k(f)) return true;
    unsigned sz = f->get_arity();
    for (unsigned i = 0; i < sz; ++i) {
        if (!get_coeff(f, i).is_one()) return false;
    }
    return true;
}

app* pb_util::mk_fresh_bool() {
    symbol name = m.mk_fresh_var_name("pb");
    func_decl_info info(m_fid, OP_PB_AUX_BOOL, 0, nullptr);
    return m.mk_const(m.mk_func_decl(name, 0, (sort *const*)nullptr, m.mk_bool_sort(), info));
}
