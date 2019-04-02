/*++
Copyright (c) 2015 Microsoft Corporation

Module Name:

    special_relations_decl_plugin.cpp

Abstract:

    <abstract>

Author:

    Nikolaj Bjorner (nbjorner) 2015-15-9.

Revision History:

--*/

#include <sstream>
#include "ast/ast.h"
#include "ast/special_relations_decl_plugin.h"



special_relations_decl_plugin::special_relations_decl_plugin():
    m_lo("linear-order"),
    m_po("partial-order"),
    m_plo("piecewise-linear-order"),
    m_to("tree-order")
{}
    
func_decl * special_relations_decl_plugin::mk_func_decl(
    decl_kind k, unsigned num_parameters, parameter const * parameters, 
    unsigned arity, sort * const * domain, sort * range)    
{
    if (arity != 2) {
        m_manager->raise_exception("special relations should have arity 2");
        return nullptr;
    }
    if (domain[0] != domain[1]) {
        m_manager->raise_exception("argument sort missmatch");
        return nullptr;
    }
    func_decl_info info(m_family_id, k, num_parameters, parameters);
    symbol name;
    switch(k) {
    case OP_SPECIAL_RELATION_PO: name = m_po; break;
    case OP_SPECIAL_RELATION_LO: name = m_lo; break;
    case OP_SPECIAL_RELATION_PLO: name = m_plo; break;
    case OP_SPECIAL_RELATION_TO: name = m_to; break;
    }
    return m_manager->mk_func_decl(name, arity, domain, m_manager->mk_bool_sort(), info);
}

void special_relations_decl_plugin::get_op_names(vector<builtin_name> & op_names, symbol const & logic) {
    if (logic == symbol::null) {
        op_names.push_back(builtin_name(m_po.bare_str(), OP_SPECIAL_RELATION_PO));
        op_names.push_back(builtin_name(m_lo.bare_str(), OP_SPECIAL_RELATION_LO));
        op_names.push_back(builtin_name(m_plo.bare_str(), OP_SPECIAL_RELATION_PLO));
        op_names.push_back(builtin_name(m_to.bare_str(), OP_SPECIAL_RELATION_TO));
    }
}

sr_property special_relations_util::get_property(func_decl* f) const {
    switch (f->get_decl_kind()) {
    case OP_SPECIAL_RELATION_PO: return sr_po;
    case OP_SPECIAL_RELATION_LO: return sr_lo;
    case OP_SPECIAL_RELATION_PLO: return sr_plo;
    case OP_SPECIAL_RELATION_TO: return sr_to;
    default:
        UNREACHABLE();
        return sr_po;
    }
}
