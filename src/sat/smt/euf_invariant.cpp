/*++
Copyright (c) 2020 Microsoft Corporation

Module Name:

    euf_invariant.cpp

Abstract:

    Check invariants for EUF solver.

Author:

    Nikolaj Bjorner (nbjorner) 2020-09-07

--*/

#include "sat/smt/euf_solver.h"

namespace euf {

    /**
       \brief Check if expressions attached to bool_variables and enodes have a consistent assignment.
       For all a, b.  root(a) == root(b) ==> get_assignment(a) == get_assignment(b)
    */

    void solver::check_eqc_bool_assignment() const {
        for (enode* n : m_egraph.nodes()) {
            VERIFY(!m.is_bool(n->get_expr()) || 
                   s().value(get_literal(n)) == s().value(get_literal(n->get_root())));        
        }
    }

    void solver::check_missing_bool_enode_propagation() const {
        for (enode* n : m_egraph.nodes()) 
            if (m.is_bool(n->get_expr()) && l_undef == s().value(get_literal(n))) {
                if (!n->is_root()) {
                    VERIFY(l_undef == s().value(get_literal(n->get_root())));
                }
                else
                    for (enode* o : enode_class(n)) {
                        VERIFY(l_undef == s().value(get_literal(o)));
                    }
            }
    }


}
