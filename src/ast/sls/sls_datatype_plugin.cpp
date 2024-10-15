/*++
Copyright (c) 2024 Microsoft Corporation

Module Name:

    sls_datatype_plugin.cpp

Abstract:

    Algebraic Datatypes for SLS
    
Author:

    Nikolaj Bjorner (nbjorner) 2024-10-14
    
--*/
#pragma once

#include "ast/sls/sls_datatype_plugin.h"

namespace sls {
    
    datatype_plugin::datatype_plugin(context& c):
        plugin(c),
        m_dt(m) {
        m_fid = m_dt.get_family_id();
    }
    
    datatype_plugin::~datatype_plugin() {}

    void datatype_plugin::add_axioms() {
        for (auto t : ctx.subterms()) {
            auto s = t->get_sort();
            if (!m_dt.is_datatype(s))
                continue;
        }
    }

    expr_ref datatype_plugin::get_value(expr* e) { return expr_ref(m); }
    void datatype_plugin::initialize() {}
    void datatype_plugin::start_propagation() {}
    void datatype_plugin::propagate_literal(sat::literal lit) {}
    bool datatype_plugin::propagate() { return false; }       
    bool datatype_plugin::is_sat() { return true; }
    void datatype_plugin::register_term(expr* e) {}
    std::ostream& datatype_plugin::display(std::ostream& out) const {
        return out;
    }
    void datatype_plugin::mk_model(model& mdl) {}
        
    void datatype_plugin::collect_statistics(statistics& st) const {}
    void datatype_plugin::reset_statistics() {}
    
}
