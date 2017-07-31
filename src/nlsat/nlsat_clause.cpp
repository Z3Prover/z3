/*++
Copyright (c) 2012 Microsoft Corporation

Module Name:

    nlsat_clause.cpp

Abstract:

    Clauses used in the Nonlinear arithmetic satisfiability procedure. 

Author:

    Leonardo de Moura (leonardo) 2012-01-02.

Revision History:

--*/
#include "nlsat/nlsat_clause.h"

namespace nlsat {

    clause::clause(unsigned id, unsigned sz, literal const * lits, bool learned, assumption_set as):
        m_id(id),
        m_size(sz),
        m_capacity(sz),
        m_learned(learned),
        m_activity(0),
        m_assumptions(as) {
        for (unsigned i = 0; i < sz; i++) {
            m_lits[i] = lits[i];
        }
    }

    bool clause::contains(literal l) const {
        for (unsigned i = 0; i < m_size; i++)
            if (m_lits[i] == l)
                return true;
        return false;
    }

    bool clause::contains(bool_var v) const {
        for (unsigned i = 0; i < m_size; i++)
            if (m_lits[i].var() == v)
                return true;
        return false;
    }

};
