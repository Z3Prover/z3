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
            expr* e = var2expr(v);
            out << " := ";
            if (e)
                out << "#" << e->get_id() << ": ";
            out << mk_bounded_pp(var2expr(v), m) << "\n";
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

    void solver::explain_assumptions() {
        m_arith_hint.reset();
        unsigned i = 0;
        for (auto const & ev : m_explanation) {
            ++i;
            auto idx = ev.ci();
            if (UINT_MAX == idx)
                continue;
            switch (m_constraint_sources[idx]) {
            case inequality_source: {
                literal lit = m_inequalities[idx];
                m_arith_hint.m_literals.push_back({ev.coeff(), lit});
                break;                
            }
            case equality_source: {
                auto [u, v] = m_equalities[idx];
                ctx.drat_log_expr(u->get_expr());
                ctx.drat_log_expr(v->get_expr());
                m_arith_hint.m_eqs.push_back({u->get_expr_id(), v->get_expr_id()});
                break;
            }
            default:
                break;
            }
        }
    }

    /**
     * It may be necessary to use the following assumption when checking Farkas claims
     * generated from bounds propagation:
     * A bound literal ax <= b is explained by a set of weighted literals
     * r1*(a1*x <= b1) + .... + r_k*(a_k*x <= b_k), where r_i > 0
     * such that there is a r >= 1
     * (r1*a1+..+r_k*a_k) = r*a, (r1*b1+..+r_k*b_k) <= r*b
     */
    sat::proof_hint const* solver::explain(sat::hint_type ty, sat::literal lit) {
        if (!ctx.use_drat())
            return nullptr;
        m_arith_hint.m_ty = ty;
        explain_assumptions();
        if (lit != sat::null_literal)
            m_arith_hint.m_literals.push_back({rational(1), ~lit});
        return &m_arith_hint;
    }

    sat::proof_hint const* solver::explain_implied_eq(euf::enode* a, euf::enode* b) {
        if (!ctx.use_drat())
            return nullptr;
        m_arith_hint.m_ty = sat::hint_type::implied_eq_h;
        explain_assumptions();
        m_arith_hint.m_diseqs.push_back({a->get_expr_id(), b->get_expr_id()});
        return &m_arith_hint;
    }
}
