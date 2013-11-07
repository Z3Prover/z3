/*++
Copyright (c) 2013 Microsoft Corporation

Module Name:

    card_decl_plugin.cpp

Abstract:

    Cardinality Constraints plugin

Author:

    Nikolaj Bjorner (nbjorner) 2013-05-11

Revision History:

--*/

#include "card_decl_plugin.h"

card_decl_plugin::card_decl_plugin():
    m_at_most_sym("at-most")
{}

func_decl * card_decl_plugin::mk_func_decl(decl_kind k, unsigned num_parameters, parameter const * parameters, 
                                           unsigned arity, sort * const * domain, sort * range) {
    SASSERT(m_manager);
    ast_manager& m = *m_manager;
    for (unsigned i = 0; i < arity; ++i) {
        if (!m.is_bool(domain[i])) {
            m.raise_exception("invalid non-Boolean sort applied to 'at-most'");
        }
    }
    if (num_parameters != 1 || !parameters[0].is_int() || parameters[0].get_int() < 0) {
        m.raise_exception("function 'at-most' expects one non-negative integer parameter");
    }
    func_decl_info info(m_family_id, OP_AT_MOST_K, 1, parameters);
    return m.mk_func_decl(m_at_most_sym, arity, domain, m.mk_bool_sort(), info);
}

void card_decl_plugin::get_op_names(svector<builtin_name> & op_names, symbol const & logic) {
    if (logic == symbol::null) {
        op_names.push_back(builtin_name(m_at_most_sym.bare_str(), OP_AT_MOST_K));
    }
}


app * card_util::mk_at_most_k(unsigned num_args, expr * const * args, unsigned k) {
    parameter param(k);
    return m.mk_app(m_fid, OP_AT_MOST_K, 1, &param, num_args, args, m.mk_bool_sort());
}

bool card_util::is_at_most_k(app *a) const {
    return is_app_of(a, m_fid, OP_AT_MOST_K);
}

bool card_util::is_at_most_k(app *a, unsigned& k) const {
    if (is_at_most_k(a)) {
        k = get_k(a);
        return true;
    }
    else {
        return false;
    }
}

unsigned card_util::get_k(app *a) const {
    SASSERT(is_at_most_k(a));
    return static_cast<unsigned>(a->get_decl()->get_parameter(0).get_int());
}

