/*++
Copyright (c) 2006 Microsoft Corporation

Module Name:

    spc_unary_inference.cpp

Abstract:

    <abstract>

Author:

    Leonardo de Moura (leonardo) 2008-02-14.

Revision History:

--*/
#include"spc_unary_inference.h"

namespace spc {

    unary_inference::unary_inference(ast_manager & m, order & ord):
        m_manager(m),
        m_order(ord),
        m_subst(m),
        m_unifier(m) {
        m_subst.reserve_offsets(1);
    }

    /**
       \brief Create the result clause. The literal at position j of \c cls in removed,
       and the substitution m_subst is applied to the resultant clause.
    */
    clause * unary_inference::mk_result(clause * cls, unsigned j) {
        sbuffer<literal> new_literals;
        unsigned num = cls->get_num_literals();
        for (unsigned i = 0; i < num; i++) {
            if (i != j) {
                literal const & l = cls->get_literal(i);
                expr_ref new_atom(m_manager);
                m_subst.apply(l.atom(), new_atom);
                new_literals.push_back(literal(new_atom, l.sign()));
            }
        }
        
        justification * js = mk_justification(cls->get_justification(), new_literals.size(), new_literals.c_ptr());
        clause * new_cls = clause::mk(m_manager, new_literals.size(), new_literals.c_ptr(), js, cls->get_scope_lvl());
        return new_cls;
    }

};
