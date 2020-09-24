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

    void solver::ensure_dual_solver() {
        if (!m_dual_solver)
            m_dual_solver = alloc(sat::dual_solver, s().rlimit());
    }

    void solver::add_root(unsigned n, sat::literal const* lits) {
        bool_var v = s().add_var(false);
        ensure_dual_solver();
        m_dual_solver->add_root(sat::literal(v, false), n, lits);
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
            expr* e = m_var2expr.get(lit.var(), nullptr);
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
            for (expr* arg : *to_app(e))
                if (!visited.get(arg->get_id(), false))
                    todo.push_back(arg);
        }

        TRACE("euf",
            for (enode* n : m_egraph.nodes())
                if (is_relevant(n))
                    tout << "relevant " << mk_bounded_pp(n->get_expr(), m) << "\n";);
        return true;
    }
}
