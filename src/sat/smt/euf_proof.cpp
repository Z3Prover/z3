/*++
Copyright (c) 2020 Microsoft Corporation

Module Name:

    euf_proof.cpp

Abstract:

    Proof logging facilities.

Author:

    Nikolaj Bjorner (nbjorner) 2020-08-25

--*/

#include "sat/smt/euf_solver.h"

namespace euf {

    void solver::log_node(expr* e) {
        if (is_app(e)) {
            symbol const& name = to_app(e)->get_name();
            s().get_drat().def_begin(e->get_id(), name);
            for (expr* arg : *to_app(e)) 
                s().get_drat().def_add_arg(arg->get_id());
            s().get_drat().def_end();
        }
        else {
            IF_VERBOSE(0, verbose_stream() << "logging binders is TBD\n");
        }
    }

    void solver::log_bool_var(sat::bool_var v, enode* n) {
        if (m_drat) {
            s().get_drat().bool_def(v, n->get_owner_id());
        }
    }

    /**
     * \brief logs antecedents to a proof trail.
     * 
     * NB with theories, this is not a pure EUF justification,
     * It is true modulo EUF and previously logged certificates
     * so it isn't necessarily an axiom over EUF, 
     * We will here leave it to the EUF checker to perform resolution steps.
     */
    void solver::log_antecedents(literal l, literal_vector const& r) {
        TRACE("euf", log_antecedents(tout, l, r););
        if (m_drat) {
            literal_vector lits;
            for (literal lit : r) lits.push_back(~lit);
            if (l != sat::null_literal)
                lits.push_back(l);
            s().get_drat().add(lits, sat::status::th(true, m.get_basic_family_id()));
        }
    }

    void solver::log_antecedents(std::ostream& out, literal l, literal_vector const& r) {
        for (sat::literal l : r) {
            enode* n = m_var2node[l.var()];
            out << ~l << ": ";
            if (!l.sign()) out << "! ";
            out << mk_pp(n->get_owner(), m) << "\n";
            SASSERT(s().value(l) == l_true);
        }
        if (l != sat::null_literal) {
            out << l << ": ";
            if (l.sign()) out << "! ";
            enode* n = m_var2node[l.var()];
            out << mk_pp(n->get_owner(), m) << "\n";            
        }
    }


}
