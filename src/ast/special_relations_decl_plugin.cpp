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
    m_to("tree-order"),
    m_tc("transitive-closure"),
    m_ac("ac-op")
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
        m_manager->raise_exception("argument sort missmatch. The two arguments should have the same sort");
        return nullptr;
    }
    if (!range && k == OP_SPECIAL_RELATION_AC)
        range = domain[0];

    if (!range) {
        range = m_manager->mk_bool_sort();
    }
    auto check_bool_range = [&]() {
        if (!m_manager->is_bool(range))
            m_manager->raise_exception("range type is expected to be Boolean for special relations");        
    };


    m_has_special_relation = true;
    func_decl_info info(m_family_id, k, num_parameters, parameters);
    symbol name;
    switch(k) {
    case OP_SPECIAL_RELATION_PO: check_bool_range();  name = m_po; break;
    case OP_SPECIAL_RELATION_LO: check_bool_range();  name = m_lo; break;
    case OP_SPECIAL_RELATION_PLO: check_bool_range();  name = m_plo; break;
    case OP_SPECIAL_RELATION_TO: check_bool_range();  name = m_to; break;
    case OP_SPECIAL_RELATION_AC: {
        if (range != domain[0])
            m_manager->raise_exception("AC operation should have the same range as domain type");
        name = m_ac;
        if (num_parameters != 1 || !parameters[0].is_ast() || !is_func_decl(parameters[0].get_ast()))
            m_manager->raise_exception("parameter to transitive closure should be a function declaration");
        func_decl* f = to_func_decl(parameters[0].get_ast());
        if (f->get_arity() != 2)
            m_manager->raise_exception("ac function should be binary");
        if (f->get_domain(0) != f->get_domain(1))
            m_manager->raise_exception("ac function should have same domain");
        if (f->get_domain(0) != f->get_range())
            m_manager->raise_exception("ac function should have same domain and range");
        break;
    }
    case OP_SPECIAL_RELATION_TC: 
        check_bool_range();
        name = m_tc; 
        if (num_parameters != 1 || !parameters[0].is_ast() || !is_func_decl(parameters[0].get_ast()))
            m_manager->raise_exception("parameter to transitive closure should be a function declaration");
        func_decl* f = to_func_decl(parameters[0].get_ast());
        if (f->get_arity() != 2)
            m_manager->raise_exception("tc relation should be binary");
        if (f->get_domain(0) != f->get_domain(1))
            m_manager->raise_exception("tc relation should have same domain");
        if (!m_manager->is_bool(f->get_range()))
            m_manager->raise_exception("tc relation should be Boolean");
        break;
    }
    return m_manager->mk_func_decl(name, arity, domain, range, info);
}

void special_relations_decl_plugin::get_op_names(svector<builtin_name> & op_names, symbol const & logic) {
    if (logic == symbol::null) {
        op_names.push_back(builtin_name(m_po.str(), OP_SPECIAL_RELATION_PO));
        op_names.push_back(builtin_name(m_lo.str(), OP_SPECIAL_RELATION_LO));
        op_names.push_back(builtin_name(m_plo.str(), OP_SPECIAL_RELATION_PLO));
        op_names.push_back(builtin_name(m_to.str(), OP_SPECIAL_RELATION_TO));
        op_names.push_back(builtin_name(m_tc.str(), OP_SPECIAL_RELATION_TC));
        op_names.push_back(builtin_name(m_ac.str(), OP_SPECIAL_RELATION_AC));
    }
}

sr_property special_relations_util::get_property(func_decl* f) const {
    switch (f->get_decl_kind()) {
    case OP_SPECIAL_RELATION_PO: return sr_po;
    case OP_SPECIAL_RELATION_LO: return sr_lo;
    case OP_SPECIAL_RELATION_PLO: return sr_plo;
    case OP_SPECIAL_RELATION_TO: return sr_to;
    case OP_SPECIAL_RELATION_TC: return sr_tc;
    case OP_SPECIAL_RELATION_AC: return sr_none;
    default:
        UNREACHABLE();
        return sr_po;
    }
}
