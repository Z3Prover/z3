/*++
Copyright (c) 2006 Microsoft Corporation

Module Name:

    spc_factoring.cpp

Abstract:

    <abstract>

Author:

    Leonardo de Moura (leonardo) 2008-02-14.

Revision History:

--*/
#include"spc_factoring.h"

namespace spc {

    /**
       \brief Create a new clause by removing literal at position j, apply substitution m_subst,
       and adding a disequality lhs != rhs.
    */
    clause * factoring::mk_eq_fact_result(clause * cls, unsigned j, expr * lhs, expr * rhs) {
        sbuffer<literal> new_literals;

        expr_ref new_eq(m_manager.mk_eq(lhs, rhs), m_manager);
        expr_ref new_eq_after_subst(m_manager);
        m_subst.apply(new_eq, new_eq_after_subst);
        new_literals.push_back(literal(new_eq_after_subst, true));

        unsigned num = cls->get_num_literals();
        for (unsigned i = 0; i < num; i++) {
            if (i != j) {
                literal const & l = cls->get_literal(i);
                expr_ref new_atom(m_manager);
                m_subst.apply(l.atom(), new_atom);
                new_literals.push_back(literal(new_atom, l.sign()));
            }
        }
        
        justification * js = mk_factoring_justification(m_manager, m_spc_fid, cls->get_justification(), new_literals.size(), 
                                                        new_literals.c_ptr());
        clause * new_cls = clause::mk(m_manager, new_literals.size(), new_literals.c_ptr(), js, cls->get_scope_lvl());
        m_stats.m_num_eq_factoring++;
        return new_cls;
    }

    /**
       \brief Try to apply equality factoring using the eq literal stored at position j.
       Assume lhs and rhs are the left hand side of this equality (they may be swapped).
    */
    void factoring::try_eq_factoring(clause * cls, unsigned j, expr * lhs, expr * rhs, ptr_vector<clause> & new_clauses) {
        literal const & l1 = cls->get_literal(j);
        sort * s = m_manager.get_sort(lhs);
        unsigned num_lits = cls->get_num_literals();
        for (unsigned i = 0; i < num_lits; i++) {
            literal const & l2 = cls->get_literal(i);
            if (i == j)
                continue;
            if (l2.sign())
                continue;
            expr * atom = l2.atom();
            if (!m_manager.is_eq(atom))
                continue;
            expr * lhs2 = to_app(atom)->get_arg(0);
            if (m_manager.get_sort(lhs2) != s)
                continue;
            expr * rhs2 = to_app(atom)->get_arg(1);
            m_subst.reset();
            if (m_unifier(lhs, lhs2, m_subst, false) && 
                (l1.is_oriented() || !m_order.greater(rhs, lhs, &m_subst)) && 
                cls->is_eligible_for_paramodulation(m_order, l1, 0, &m_subst)) {
                new_clauses.push_back(mk_eq_fact_result(cls, j, rhs, rhs2));
            }
            m_subst.reset();
            if (m_unifier(lhs, rhs2, m_subst, false) &&
                (l1.is_oriented() || !m_order.greater(rhs, lhs, &m_subst)) && 
                cls->is_eligible_for_paramodulation(m_order, l1, 0, &m_subst)) {
                new_clauses.push_back(mk_eq_fact_result(cls, j, rhs, lhs2));
            }
        }
    }

    /**
       \brief Try to apply equality factoring using the eq literal stored at position i.
    */
    void factoring::try_eq_factoring(clause * cls, unsigned i, ptr_vector<clause> & new_clauses) {
        if (cls->get_num_pos_literals() <= 1)
            return;
        literal const & l = cls->get_literal(i);
        app * eq   = to_app(l.atom());
        expr * lhs = eq->get_arg(0);
        expr * rhs = eq->get_arg(1);
        if (l.is_oriented()) {
            if (!l.is_left()) 
                std::swap(lhs, rhs);
            try_eq_factoring(cls, i, lhs, rhs, new_clauses);
        }
        else {
            try_eq_factoring(cls, i, lhs, rhs, new_clauses);
            try_eq_factoring(cls, i, rhs, lhs, new_clauses);
        }
    }

    /**
       \brief Try to apply (ordering) factoring rule.
    */
    void factoring::try_factoring(clause * cls, unsigned j, ptr_vector<clause> & new_clauses) {
        literal const & l1 = cls->get_literal(j);
        if (l1.sign() && cls->get_num_neg_literals() <= 1)
            return;
        if (!l1.sign() && cls->get_num_pos_literals() <= 1)
            return;
        unsigned num = cls->get_num_literals();
        for (unsigned i = 0; i < num; i++) {
            if (i == j)
                continue;
            literal const & l2 = cls->get_literal(i);
            if (l1.sign() != l2.sign())
                continue;
            m_subst.reset();
            if (m_unifier(l1.atom(), l2.atom(), m_subst, false) &&
                cls->is_eligible_for_resolution(m_order, l1, 0, &m_subst)) {
                new_clauses.push_back(mk_result(cls, i));
                m_stats.m_num_factoring++;
            }
        }
    }

    /**
       \brief Apply factoring rule on the given clause.
       Store the produced clauses into new_clauses.
    */
    void factoring::operator()(clause * cls, ptr_vector<clause> & new_clauses) {
        if (cls->get_num_pos_literals() <= 1 && cls->get_num_neg_literals() <= 1)
            return;

        m_subst.reserve_vars(cls->get_num_vars());
        unsigned num = cls->get_num_literals();
        for (unsigned i = 0; i < num; i++) {
            literal const & l = cls->get_literal(i);
            expr * atom = l.atom();
            // remark: if the clause has selected literals then the literal will not be eligible
            // for paramodulation and eq_resolution will not be applied.
            if (!l.sign() && m_manager.is_eq(atom) && !cls->has_sel_lit()) 
                try_eq_factoring(cls, i, new_clauses);
            if (l.is_selected() || !cls->has_sel_lit())
                try_factoring(cls, i, new_clauses);
        }
    }
  
};
