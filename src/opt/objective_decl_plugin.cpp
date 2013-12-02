/*++
Copyright (c) 2013 Microsoft Corporation

Module Name:

    objective_decl_plugin.cpp

Abstract:
    Abstract data-type for compound objectives.

Author:

    Nikolaj Bjorner (nbjorner) 2013-11-21

Notes:

--*/

#include "objective_decl_plugin.h"

namespace opt{
    objective_decl_plugin::objective_decl_plugin() {}

    objective_decl_plugin::~objective_decl_plugin() {}
        
    sort * objective_decl_plugin::mk_sort(decl_kind k, unsigned num_parameters, parameter const * parameters) {
        SASSERT(k == OBJECTIVE_SORT);
        SASSERT(num_parameters == 0);
        return m_manager->mk_sort(symbol("objective"), sort_info(get_family_id(), k));
    }

    symbol objective_decl_plugin::get_name(obj_kind k) const {
        switch(k) {
        case OP_MINIMIZE: return symbol("minimize");
        case OP_MAXIMIZE: return symbol("maximize");
        case OP_LEX: return symbol("lex");
        case OP_BOX: return symbol("box");
        case OP_PARETO: return symbol("pareto");
        default:
            UNREACHABLE();
            return symbol();
        }
    }
        
    func_decl * objective_decl_plugin::mk_func_decl(
        decl_kind k, unsigned num_parameters, parameter const * parameters, 
        unsigned arity, sort * const * domain, sort * range) {
        SASSERT(num_parameters == 0);
        symbol name = get_name(static_cast<obj_kind>(k));
        func_decl_info info(get_family_id(), k, num_parameters, parameters);
        return m_manager->mk_func_decl(name, arity, domain, range, info);
    }
    
    void objective_decl_plugin::get_op_names(svector<builtin_name> & op_names, symbol const & logic) {
        if (logic == symbol::null) {
            op_names.push_back(builtin_name(get_name(OP_MAXIMIZE).bare_str(), OP_MAXIMIZE));
            op_names.push_back(builtin_name(get_name(OP_MINIMIZE).bare_str(), OP_MINIMIZE));
            op_names.push_back(builtin_name(get_name(OP_LEX).bare_str(), OP_LEX));
            op_names.push_back(builtin_name(get_name(OP_BOX).bare_str(), OP_BOX));
            op_names.push_back(builtin_name(get_name(OP_PARETO).bare_str(), OP_PARETO));
        }
    }


    objective_util::objective_util(ast_manager& m): m(m), m_fid(m.get_family_id("objective")) {}

    app* objective_util::mk_max(expr_ref& e) {
        expr* es[1] = { e };
        return m.mk_app(m_fid, OP_MAXIMIZE, 0, 0, 1, es);
    }
    app* objective_util::mk_min(expr_ref& e) {
        expr* es[1] = { e };
        return m.mk_app(m_fid, OP_MINIMIZE, 0, 0, 1, es);
    }
    app* objective_util::mk_maxsat(symbol id) {
        return m.mk_const(id, m.mk_sort(m_fid, OBJECTIVE_SORT, 0, 0));
    }
    app* objective_util::mk_lex(unsigned sz, expr * const * children) {
        return m.mk_app(m_fid, OP_LEX, 0, 0, sz, children);
    }
    app* objective_util::mk_box(unsigned sz, expr * const * children) {
        return m.mk_app(m_fid, OP_BOX, 0, 0, sz, children);
    }
    app* objective_util::mk_pareto(unsigned sz, expr * const * children) {
        return m.mk_app(m_fid, OP_PARETO, 0, 0, sz, children);
    }
    
}
