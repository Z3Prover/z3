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
            out << lp().constraints();
            lp().print_terms(out);
            // the tableau
            lp().pp(out).print();
            for (unsigned j = 0; j < lp().number_of_vars(); j++) {
                lp().print_column_info(j, out);
            }
        
        if (m_nla) {
            m_nla->display(out);
        }
        unsigned nv = get_num_vars();
        for (unsigned v = 0; v < nv; ++v) {
            auto t = get_tv(v);
            auto vi = lp().external_to_column_index(v);
            out << "v" << v << " ";
            if (t.is_null()) out << "null"; else out << (t.is_term() ? "t" : "j") << vi;
            if (m_nla && m_nla->use_nra_model() && can_get_ivalue(v)) {
                scoped_anum an(m_nla->am());
                m_nla->am().display(out << " = ", nl_value(v, an));
            }
            else if (can_get_value(v)) out << " = " << get_value(v);
            if (is_int(v)) out << ", int";
            if (ctx.is_shared(var2enode(v))) out << ", shared";
            out << " := " << mk_bounded_pp(var2expr(v), m) << "\n";
        }
        return out; 
    }

    std::ostream& solver::display_justification(std::ostream& out, sat::ext_justification_idx idx) const { 
        auto& jst = euf::th_propagation::from_index(idx);
        for (auto lit : euf::th_propagation::lits(jst))
            out << lit << " ";
        for (auto eq : euf::th_propagation::eqs(jst))
            out << eq.first->get_expr_id() << " == " << eq.second->get_expr_id() << " ";
        return out;
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
