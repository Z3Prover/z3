/*++
Copyright (c) 2006 Microsoft Corporation

Module Name:

    spc_eq_resolution.cpp

Abstract:

    <abstract>

Author:

    Leonardo de Moura (leonardo) 2008-02-14.

Revision History:

--*/
#include"spc_eq_resolution.h"

namespace spc {

    /**
       \brief Apply equality resolution rule on the given clause.
       Store the produced clauses in new_clauses.
    */
    void eq_resolution::operator()(clause * cls, ptr_vector<clause> & new_clauses) {
        m_subst.reserve_vars(cls->get_num_vars());
        unsigned num = cls->get_num_literals();
        for (unsigned i = 0; i < num; i++) {
            literal const & l = cls->get_literal(i);
            expr * atom = l.atom();
            if (l.sign() && m_manager.is_eq(atom)) {
                expr * lhs = to_app(atom)->get_arg(0);
                expr * rhs = to_app(atom)->get_arg(1);
                m_subst.reset();
                if (m_unifier(lhs, rhs, m_subst, false) && cls->is_eligible_for_resolution(m_order, l, 0, &m_subst)) {
                    m_stats.m_num_eq_resolution++;
                    new_clauses.push_back(mk_result(cls, i));
                }
            }
        }
    }
};
