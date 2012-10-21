/*++
Copyright (c) 2006 Microsoft Corporation

Module Name:

    spc_der.cpp

Abstract:

    <abstract>

Author:

    Leonardo de Moura (leonardo) 2008-02-17.

Revision History:

--*/
#include"spc_der.h"
#include"occurs.h"

namespace spc {

    der::der(ast_manager & m):
        m_manager(m),
        m_subst(m),
        m_spc_fid(m.get_family_id("spc")) {
        m_subst.reserve_offsets(1);
    }

    void der::apply(clause * cls, unsigned j, expr * lhs, expr * rhs) {
        TRACE("der", tout << "applying der at: " << j << "\n"; cls->display(tout, m_manager); tout << "\n";);
        m_subst.reserve_vars(cls->get_num_vars());
        m_subst.reset();
        m_subst.insert(expr_offset(lhs, 0), expr_offset(rhs, 0));
        literal_buffer new_lits(m_manager);
        unsigned num_lits = cls->get_num_literals();
        for (unsigned i = 0; i < num_lits; i++) {
            if (i != j) {
                literal const & l = cls->get_literal(i);
                expr_ref new_atom(m_manager);
                m_subst.apply(l.atom(), new_atom);
                new_lits.push_back(literal(new_atom, l.sign()));
            }
        }
        justification * js = mk_der_justification(m_manager, m_spc_fid, cls->get_justification(), new_lits.size(), new_lits.c_ptr());
        cls->update_lits(m_manager, new_lits.size(), new_lits.c_ptr(), js);
    }

    bool der::apply(clause * cls) {
        unsigned num_lits = cls->get_num_literals();
        for (unsigned i = 0; i < num_lits; i++) {
            literal const & l = cls->get_literal(i);
            if (l.sign() && m_manager.is_eq(l.atom())) {
                expr * lhs = l.lhs();
                expr * rhs = l.rhs();
                if (is_var(lhs) && !occurs(lhs, rhs)) {
                    apply(cls, i, lhs, rhs);
                    return true;
                }
                else if (is_var(rhs) && !occurs(rhs, lhs)) {
                    apply(cls, i, rhs, lhs);
                    return true;
                }
            }
        }
        return false;
    }
    
    /**
       \brief Clause cls is destructively updated.
    */
    void der::operator()(clause * cls) {
        while(apply(cls))
            ;
    }


};

