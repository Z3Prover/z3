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

    bool solver::is_relevant(expr* e) const { 
        return m_relevant_expr_ids.get(e->get_id(), true); 
    }

    bool solver::is_relevant(enode* n) const { 
        return m_relevant_expr_ids.get(n->get_expr_id(), true); 
    }

    void solver::ensure_dual_solver() {
        if (!m_dual_solver) {
            m_dual_solver = alloc(sat::dual_solver, s().rlimit());
            for (unsigned i = s().num_user_scopes(); i-- > 0; )
                m_dual_solver->push();
        }
    }

    void solver::add_root(unsigned n, sat::literal const* lits) {
        ensure_dual_solver();
        m_dual_solver->add_root(n, lits);
    }

    void solver::add_aux(unsigned n, sat::literal const* lits) {
        ensure_dual_solver();
        m_dual_solver->add_aux(n, lits);
    }

    void solver::track_relevancy(sat::bool_var v) {
        ensure_dual_solver();
        m_dual_solver->track_relevancy(v);
    }

    bool solver::init_relevancy() {
        m_relevant_expr_ids.reset();
        bool_vector visited;
        ptr_vector<expr> todo;
        if (!relevancy_enabled())
            return true;
        if (!m_dual_solver)
            return true;
        if (!(*m_dual_solver)(s()))
            return false;
        unsigned max_id = 0;
        for (enode* n : m_egraph.nodes())
            max_id = std::max(max_id, n->get_expr_id());
        m_relevant_expr_ids.resize(max_id + 1, false);
        auto const& core = m_dual_solver->core();
        for (auto lit : core) {
            expr* e = m_bool_var2expr.get(lit.var(), nullptr);
            if (e)
                todo.push_back(e);
        }
        for (unsigned i = 0; i < todo.size(); ++i) {
            expr* e = todo[i];
            if (visited.get(e->get_id(), false))
                continue;
            visited.setx(e->get_id(), true, false);
            if (!si.is_bool_op(e)) 
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

        TRACE("euf",
            for (enode* n : m_egraph.nodes())
                if (is_relevant(n)) 
                    tout << "relevant " << n->get_expr_id() << " [r" << n->get_root_id() << "]: " << mk_bounded_pp(n->get_expr(), m) << "\n";);
              return true;
    }
}
