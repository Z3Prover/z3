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
                   s().value(enode2literal(n)) == s().value(enode2literal(n->get_root())));
        }
    }

    void solver::check_missing_bool_enode_propagation() const {
        for (enode* n : m_egraph.nodes()) 
            if (m.is_bool(n->get_expr()) && l_undef == s().value(enode2literal(n))) {
                if (!n->is_root()) {
                    VERIFY(l_undef == s().value(enode2literal(n->get_root())));
                }
                else
                    for (enode* o : enode_class(n)) {
                        VERIFY(l_undef == s().value(enode2literal(o)));
                    }
            }
    }

    void solver::check_missing_eq_propagation() const {
        if (s().inconsistent())
            return;
        for (enode* n : m_egraph.nodes())
            if (m.is_false(n->get_root()->get_expr()) && 
                m.is_eq(n->get_expr()) &&
                !m.is_bool(n->get_app()->get_arg(0)) && 
                (n->get_arg(0)->get_root() == n->get_arg(1)->get_root())) {
                enable_trace("euf");
                TRACE("euf", display(tout << n->get_expr_id() << ": " << mk_pp(n->get_expr(), m) << "\n" 
                                     << "#" << n->get_arg(0)->get_expr_id() << " == #" << n->get_arg(1)->get_expr_id() << " r: " << n->get_arg(0)->get_root_id() << "\n");
                      );
                UNREACHABLE();
            }
    }


}
