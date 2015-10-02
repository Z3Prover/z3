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

#include "pb_decl_plugin.h"

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
                rational r = p.get_rational();
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
        return 0;
    }
}

void pb_decl_plugin::get_op_names(svector<builtin_name> & op_names, symbol const & logic) {
    if (logic == symbol::null) {
        op_names.push_back(builtin_name(m_at_most_sym.bare_str(), OP_AT_MOST_K));
        op_names.push_back(builtin_name(m_at_least_sym.bare_str(), OP_AT_LEAST_K));
        op_names.push_back(builtin_name(m_pble_sym.bare_str(), OP_PB_LE));
        op_names.push_back(builtin_name(m_pbge_sym.bare_str(), OP_PB_GE));
        op_names.push_back(builtin_name(m_pbeq_sym.bare_str(), OP_PB_EQ));
    }
}

app * pb_util::mk_le(unsigned num_args, rational const * coeffs, expr * const * args, rational const& k) {
    vector<parameter> params;
    params.push_back(parameter(k));
    for (unsigned i = 0; i < num_args; ++i) {
        params.push_back(parameter(coeffs[i]));
    }
    return m.mk_app(m_fid, OP_PB_LE, params.size(), params.c_ptr(), num_args, args, m.mk_bool_sort());
}

app * pb_util::mk_ge(unsigned num_args, rational const * coeffs, expr * const * args, rational const& k) {
    vector<parameter> params;
    params.push_back(parameter(k));
    for (unsigned i = 0; i < num_args; ++i) {
        params.push_back(parameter(coeffs[i]));
    }
    return m.mk_app(m_fid, OP_PB_GE, params.size(), params.c_ptr(), num_args, args, m.mk_bool_sort());
}

app * pb_util::mk_eq(unsigned num_args, rational const * coeffs, expr * const * args, rational const& k) {
    vector<parameter> params;
    params.push_back(parameter(k));
    for (unsigned i = 0; i < num_args; ++i) {
        params.push_back(parameter(coeffs[i]));
    }
    return m.mk_app(m_fid, OP_PB_EQ, params.size(), params.c_ptr(), num_args, args, m.mk_bool_sort());
}

// ax + by < k
// <=>
// -ax - by >= -k + 1
// <=>
// a(1-x) + b(1-y) >= -k + a + b + 1
app * pb_util::mk_lt(unsigned num_args, rational const * _coeffs, expr * const * _args, rational const& _k) {
    vector<rational> coeffs;
    rational k(_k);
    expr_ref_vector args(m);
    expr* f;
    rational d(denominator(k));
    for (unsigned i = 0; i < num_args; ++i) {
        coeffs.push_back(_coeffs[i]);
        d = lcm(d, denominator(coeffs[i]));
        if (m.is_not(_args[i], f)) {
            args.push_back(f);
        }
        else {
            args.push_back(m.mk_not(_args[i]));
        }
    }
    if (!d.is_one()) {
        k *= d;
        for (unsigned i = 0; i < num_args; ++i) {
            coeffs[i] *= d;        
        }
    }
    k.neg();
    k += rational::one();
    for (unsigned i = 0; i < num_args; ++i) {
        k += coeffs[i];
    }
    return mk_ge(num_args, coeffs.c_ptr(), args.c_ptr(), k);
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
    func_decl_info info(m_fid, OP_PB_AUX_BOOL, 0, 0);
    return m.mk_const(m.mk_func_decl(name, 0, (sort *const*)0, m.mk_bool_sort(), info));
}
