/*++
Copyright (c) 2020 Microsoft Corporation

Module Name:

    arith_diagnostics.cpp

Abstract:

    Theory plugin for arithmetic

Author:

    Nikolaj Bjorner (nbjorner) 2020-09-08

--*/

#include "sat/smt/euf_solver.h"
#include "sat/smt/arith_solver.h"


namespace arith {

    
    std::ostream& solver::display(std::ostream& out) const { 
        lp().display(out);
        
        if (m_nla) {
            m_nla->display(out);
        }
        unsigned nv = get_num_vars();
        for (unsigned v = 0; v < nv; ++v) {
            auto t = get_tv(v);
            auto vi = lp().external_to_column_index(v);
            out << "v" << v << " ";
            if (is_bool(v)) {
                euf::enode* n = var2enode(v);
                api_bound* b = nullptr;
                if (m_bool_var2bound.find(n->bool_var(), b)) {
                    sat::literal lit = b->get_lit();
                    out << lit << " " << s().value(lit);
                }
            }
            else {
                if (t.is_null()) 
                    out << "null"; 
                else 
                    out << (t.is_term() ? "t" : "j") << vi;
                if (m_nla && m_nla->use_nra_model() && is_registered_var(v)) {
                    scoped_anum an(m_nla->am());
                    m_nla->am().display(out << " = ", nl_value(v, an));
                }
                else if (can_get_value(v) && !m_solver->has_changed_columns())  
                    out << " = " << get_value(v);
                if (is_int(v)) 
                    out << ", int";
                if (ctx.is_shared(var2enode(v))) 
                    out << ", shared";
            }
            out << " := " << mk_bounded_pp(var2expr(v), m) << "\n";
        }
        return out; 
    }

    std::ostream& solver::display_justification(std::ostream& out, sat::ext_justification_idx idx) const { 
        return euf::th_explain::from_index(idx).display(out);
    }

    std::ostream& solver::display_constraint(std::ostream& out, sat::ext_constraint_idx idx) const { 
        return display_justification(out, idx);
    }

    void solver::collect_statistics(statistics& st) const {
        m_stats.collect_statistics(st);
        lp().settings().stats().collect_statistics(st);
        if (m_nla) m_nla->collect_statistics(st);
    }
}
