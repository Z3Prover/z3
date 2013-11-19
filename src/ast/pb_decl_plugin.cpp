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
    m_pble_sym("pble")
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
    switch(k) {
    case OP_AT_MOST_K: {
        if (num_parameters != 1 || !parameters[0].is_int() || parameters[0].get_int() < 0) {
            m.raise_exception("function 'at-most' expects one non-negative integer parameter");
        }
        func_decl_info info(m_family_id, OP_AT_MOST_K, 1, parameters);
        return m.mk_func_decl(m_at_most_sym, arity, domain, m.mk_bool_sort(), info);
    }
    case OP_PB_LE: {
        if (num_parameters != 1 + arity || !parameters[0].is_int()) {
            m.raise_exception("function 'pble' expects arity+1 integer parameters");
        }
        for (unsigned i = 1; i < num_parameters; ++i) {
            if (!parameters[i].is_int()) {
                m.raise_exception("function 'pble' expects arity+1 integer parameters");
            }
        }
        func_decl_info info(m_family_id, OP_PB_LE, num_parameters, parameters);
        return m.mk_func_decl(m_pble_sym, arity, domain, m.mk_bool_sort(), info);
    }
    default:
        UNREACHABLE();
        return 0;
    }
}

void pb_decl_plugin::get_op_names(svector<builtin_name> & op_names, symbol const & logic) {
    if (logic == symbol::null) {
        op_names.push_back(builtin_name(m_at_most_sym.bare_str(), OP_AT_MOST_K));
        op_names.push_back(builtin_name(m_pble_sym.bare_str(), OP_PB_LE));
    }
}


app * pb_util::mk_at_most_k(unsigned num_args, expr * const * args, unsigned k) {
    parameter param(k);
    return m.mk_app(m_fid, OP_AT_MOST_K, 1, &param, num_args, args, m.mk_bool_sort());
}

app * pb_util::mk_le(unsigned num_args, int const * coeffs, expr * const * args, int k) {
    vector<parameter> params;
    params.push_back(parameter(k));
    for (unsigned i = 0; i < num_args; ++i) {
        params.push_back(parameter(coeffs[i]));
    }
    return m.mk_app(m_fid, OP_PB_LE, params.size(), params.c_ptr(), num_args, args, m.mk_bool_sort());
}


bool pb_util::is_at_most_k(app *a) const {
    return is_app_of(a, m_fid, OP_AT_MOST_K);
}

bool pb_util::is_at_most_k(app *a, unsigned& k) const {
    if (is_at_most_k(a)) {
        k = get_k(a);
        return true;
    }
    else {
        return false;
    }
}

int pb_util::get_k(app *a) const {
    SASSERT(is_at_most_k(a) || is_le(a));
    return a->get_decl()->get_parameter(0).get_int();
}


bool pb_util::is_le(app *a) const {
    return is_app_of(a, m_fid, OP_PB_LE);
}

bool pb_util::is_le(app* a, int& k) const {
    if (is_le(a)) {
        k = get_k(a);
        return true;
    }
    else {
        return false;
    }
}

int pb_util::get_le_coeff(app* a, unsigned index) {
    if (is_at_most_k(a)) {
        return 1;
    }
    SASSERT(is_le(a));
    SASSERT(1 + index < a->get_decl()->get_num_parameters());
    return a->get_decl()->get_parameter(index + 1).get_int();
}


