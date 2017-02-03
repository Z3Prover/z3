/*++
Copyright (c) 2014 Microsoft Corporation

Module Name:

    sat_drat.cpp

Abstract:
   
    Produce DRAT proofs.

Author:

    Nikolaj Bjorner (nbjorner) 2017-2-3

Notes:

--*/
#include "sat_solver.h"
#include "sat_drat.h"


namespace sat {
    drat::drat(solver& s):
        s(s),
        m_out(0)
    {
        if (s.m_config.m_drat) {
            m_out = alloc(std::ofstream, "proof.drat");
        }
    }

    drat::~drat() {
        dealloc(m_out);
    }
    void drat::add_empty() {
        (*m_out) << "0\n";
    }
    void drat::add_literal(literal l) {
        (*m_out) << l << " 0\n";
    }
    void drat::add_binary(literal l1, literal l2) {
        (*m_out) << l1 << " " << l2 << " 0\n";
    }
    void drat::add_ternary(literal l1, literal l2, literal l3) {
        (*m_out) << l1 << " " << l2 << " " << l3 << " 0\n";
    }
    void drat::add_clause(clause& c) {
        unsigned sz = c.size();
        for (unsigned i = 0; i < sz; ++i) {
            (*m_out) << c[i] << " ";
        }
        (*m_out) << "0\n";
    }
    void drat::del_literal(literal l) {
        (*m_out) << "d ";
        add_literal(l);
    }
    void drat::del_binary(literal l1, literal l2) {
        (*m_out) << "d ";
        add_binary(l1, l2);
    }
    void drat::del_clause(clause& c) {
        (*m_out) << "d ";
        add_clause(c);
    }
}
