/*++
Copyright (c) 2025 Microsoft Corporation

Module Name:

    nseq_state.cpp

Abstract:

    State management for the Nielsen-based string theory solver.

Author:

    Clemens Eisenhofer
    Nikolaj Bjorner (nbjorner) 2025-2-28

--*/

#include "ast/ast_pp.h"
#include "ast/ast_ll_pp.h"
#include "smt/nseq_state.h"

namespace smt {

    nseq_state::nseq_state(ast_manager& m, seq_util& u)
        : m(m),
          m_util(u),
          m_eq_id(0),
          m_axioms(m),
          m_axioms_head(0),
          m_length_apps(m),
          m_length_exprs(m) {
    }

    void nseq_state::push_scope() {
        m_dm.push_scope();
        m_trail.push_scope();
        m_trail.push(value_trail<unsigned>(m_axioms_head));
        m_eqs.push_scope();
        m_neqs.push_scope();
        m_mems.push_scope();
        m_preds.push_scope();
    }

    void nseq_state::pop_scope(unsigned num_scopes) {
        m_trail.pop_scope(num_scopes);
        m_dm.pop_scope(num_scopes);
        m_eqs.pop_scope(num_scopes);
        m_neqs.pop_scope(num_scopes);
        m_mems.pop_scope(num_scopes);
        m_preds.pop_scope(num_scopes);
    }

    void nseq_state::reset() {
        m_axioms.reset();
        m_axiom_set.reset();
        m_axioms_head = 0;
        m_has_length.reset();
        m_length_apps.reset();
        m_length_exprs.reset();
        m_eq_id = 0;
    }

    unsigned nseq_state::add_eq(expr* l, expr* r, nseq_dependency* dep) {
        expr_ref_vector lhs(m), rhs(m);
        m_util.str.get_concat_units(l, lhs);
        m_util.str.get_concat_units(r, rhs);
        unsigned id = m_eq_id++;
        m_eqs.push_back(nseq_eq(id, lhs, rhs, dep));
        m_stats.m_num_eqs++;
        return id;
    }

    void nseq_state::add_ne(expr* l, expr* r, nseq_dependency* dep) {
        expr_ref el(l, m), er(r, m);
        m_neqs.push_back(nseq_ne(el, er, dep));
        m_stats.m_num_neqs++;
    }

    void nseq_state::add_mem(expr* s, expr* re, bool sign, nseq_dependency* dep) {
        expr_ref es(s, m), ere(re, m);
        m_mems.push_back(nseq_mem(es, ere, sign, dep));
        m_stats.m_num_memberships++;
    }

    void nseq_state::add_pred(nseq_pred_kind kind, expr* a1, expr* a2, bool sign, nseq_dependency* dep) {
        expr_ref ea1(a1, m), ea2(a2, m);
        m_preds.push_back(nseq_pred(kind, ea1, ea2, sign, dep));
        m_stats.m_num_predicates++;
    }

    bool nseq_state::enqueue_axiom(expr* e) {
        if (m_axiom_set.contains(e))
            return false;
        m_axiom_set.insert(e);
        m_axioms.push_back(e);
        return true;
    }

    void nseq_state::add_length(expr* len_app, expr* e, trail_stack& ts) {
        if (m_has_length.contains(e))
            return;
        m_length_apps.push_back(len_app);
        m_length_exprs.push_back(e);
        m_has_length.insert(e);
        ts.push(push_back_vector<expr_ref_vector>(m_length_apps));
        ts.push(push_back_vector<expr_ref_vector>(m_length_exprs));
        ts.push(insert_obj_trail<expr>(m_has_length, e));
    }

    void nseq_state::linearize(nseq_dependency* dep, enode_pair_vector& eqs, literal_vector& lits) const {
        if (!dep)
            return;
        svector<nseq_assumption> assumptions;
        m_dm.linearize(dep, assumptions);
        for (auto const& a : assumptions) {
            if (a.n1 != nullptr)
                eqs.push_back(enode_pair(a.n1, a.n2));
            else if (a.lit != null_literal)
                lits.push_back(a.lit);
        }
    }

    std::ostream& nseq_state::display(std::ostream& out) const {
        if (!m_eqs.empty()) {
            out << "equations:\n";
            for (auto const& eq : m_eqs) {
                out << "  [" << eq.id() << "] ";
                for (auto* e : eq.lhs()) out << mk_bounded_pp(e, m, 2) << " ";
                out << "= ";
                for (auto* e : eq.rhs()) out << mk_bounded_pp(e, m, 2) << " ";
                out << "\n";
            }
        }
        if (!m_neqs.empty()) {
            out << "disequalities: " << m_neqs.size() << "\n";
        }
        if (!m_mems.empty()) {
            out << "memberships: " << m_mems.size() << "\n";
        }
        if (!m_preds.empty()) {
            out << "predicates: " << m_preds.size() << "\n";
        }
        return out;
    }
}
