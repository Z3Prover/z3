/*++
Copyright (c) 2020 Microsoft Corporation

Module Name:

    euf_relevancy.cpp

Abstract:

    Features for relevancy tracking.
    A reduced (minimal) implicant is extracted by running a dual solver.
    Then the literals in the implicant are used as a basis for marking
    subterms relevant.

Author:

    Nikolaj Bjorner (nbjorner) 2020-09-22

--*/

#include "sat/smt/euf_solver.h"

namespace euf {

    void solver::add_auto_relevant(expr* e) {
        if (!relevancy_enabled())
            return;
        for (; m_auto_relevant_scopes > 0; --m_auto_relevant_scopes) 
            m_auto_relevant_lim.push_back(m_auto_relevant.size());
        // std::cout << "add-auto " << e->get_id() << " " << mk_bounded_pp(e, m) << "\n";
        m_auto_relevant.push_back(e);
    }
    
    void solver::pop_relevant(unsigned n) {
        if (m_auto_relevant_scopes >= n) {
            m_auto_relevant_scopes -= n;
            return;
        }
        n -= m_auto_relevant_scopes;
        m_auto_relevant_scopes = 0;
        unsigned top = m_auto_relevant_lim.size() - n;
        unsigned lim = m_auto_relevant_lim[top];
        m_auto_relevant_lim.shrink(top);
        m_auto_relevant.shrink(lim);        
    }
    
    void solver::push_relevant() {
        ++m_auto_relevant_scopes;
    }

    bool solver::is_relevant(expr* e) const { 
        return m_relevant_expr_ids.get(e->get_id(), true); 
    }

    bool solver::is_relevant(enode* n) const { 
        return m_relevant_expr_ids.get(n->get_expr_id(), true); 
    }

    void solver::ensure_dual_solver() {
        if (m_dual_solver)
            return;
        m_dual_solver = alloc(sat::dual_solver, s().rlimit());
        for (unsigned i = s().num_user_scopes(); i-- > 0; )
            m_dual_solver->push();        
    }

    /**
     * Add a root clause. Root clauses must all be satisfied by the 
     * final assignment. If a clause is added above search level it
     * is subject to removal on backtracking. These clauses are therefore
     * not tracked.
     */
    void solver::add_root(unsigned n, sat::literal const* lits) {
        if (!relevancy_enabled())
            return;
        ensure_dual_solver();
        m_dual_solver->add_root(n, lits);
    }

    void solver::add_aux(unsigned n, sat::literal const* lits) {
        if (!relevancy_enabled())
            return;
        ensure_dual_solver();
        m_dual_solver->add_aux(n, lits);
    }

    void solver::track_relevancy(sat::bool_var v) {
        ensure_dual_solver();
        m_dual_solver->track_relevancy(v);
    }

    bool solver::init_relevancy1() {
        m_relevant_expr_ids.reset();
        if (!relevancy_enabled())
            return true;
        if (!m_dual_solver)
            return true;
        if (!(*m_dual_solver)(s()))
            return false;
        init_relevant_expr_ids();
        
        for (auto lit : m_dual_solver->core()) 
            push_relevant(lit.var());

        relevant_subterms();

        return true;
    }

    void solver::push_relevant(sat::bool_var v) {
        expr* e = m_bool_var2expr.get(v, nullptr);
        if (e)
            m_relevant_todo.push_back(e);
    }


    bool solver::init_relevancy2() {
        m_relevant_expr_ids.reset();
        if (!relevancy_enabled())
            return true;
        init_relevant_expr_ids();
        for (unsigned i = 0; i < s().trail_size(); ++i) {
            sat::literal l = s().trail_literal(i);
            auto v = l.var();
            auto j = s().get_justification(v);
            switch (j.get_kind()) {
            case sat::justification::kind::BINARY:
            case sat::justification::kind::TERNARY:
            case sat::justification::kind::CLAUSE:
            case sat::justification::kind::EXT_JUSTIFICATION:
                push_relevant(l.var());
                break;
            case sat::justification::kind::NONE: 
                for (auto const& w : s().get_wlist(~l)) {
                    if (w.is_binary_non_learned_clause()) {
                        if (is_propagated(w.get_literal()))
                            continue;
                    }
                    else if (w.is_binary_clause())
                        continue;
                    else if (w.is_ternary_clause()) {
                        if (is_propagated(w.get_literal1()))
                            continue;
                        if (is_propagated(w.get_literal2()))
                            continue;
                    }
                    else if (w.is_clause()) {
                        if (is_propagated(w.get_blocked_literal()))
                            continue;
                    }
                    push_relevant(l.var());
                    break;
                }
                break;            
            }
        }
        relevant_subterms();
        return true;
    }

    bool solver::is_propagated(sat::literal lit) {
        return s().value(lit) == l_true && !s().get_justification(lit.var()).is_none();
    }

    void solver::init_relevant_expr_ids() {
        unsigned max_id = 0;
        for (enode* n : m_egraph.nodes())
            max_id = std::max(max_id, n->get_expr_id());
        m_relevant_expr_ids.resize(max_id + 1, false);
        m_relevant_todo.reset();
        m_relevant_todo.append(m_auto_relevant);
    }

    void solver::relevant_subterms() {
        ptr_vector<expr>& todo = m_relevant_todo;
        bool_vector& visited = m_relevant_visited;
        for (unsigned i = 0; i < todo.size(); ++i) {
            expr* e = todo[i];
            if (visited.get(e->get_id(), false))
                continue;
            visited.setx(e->get_id(), true, false);
            if (si.is_bool_op(e))
                continue;
            else
                m_relevant_expr_ids.setx(e->get_id(), true, false);
            if (!is_app(e))
                continue;
            expr* c = nullptr, *th = nullptr, *el = nullptr;
            if (m.is_ite(e, c, th, el) && get_enode(c)) {
                sat::literal lit = expr2literal(c);
                todo.push_back(c);
                switch (s().value(lit)) {
                case l_true:
                    todo.push_back(th);
                    break;
                case l_false:
                    todo.push_back(el);
                    break;
                default:
                    todo.push_back(th);
                    todo.push_back(el);
                    break;
                }
                continue;
            }
            for (expr* arg : *to_app(e))
                todo.push_back(arg);
        }

        for (auto * e : todo)
            visited[e->get_id()] = false;

        TRACE("euf",
            for (enode* n : m_egraph.nodes())
                if (is_relevant(n))
                    tout << "relevant " << n->get_expr_id() << " [r" << n->get_root_id() << "]: " << mk_bounded_pp(n->get_expr(), m) << "\n";);
    }
}
