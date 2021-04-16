/*++
Copyright (c) 2021 Microsoft Corporation

Module Name:

    polysat bit_constraint

Author:

    Nikolaj Bjorner (nbjorner) 2021-03-19
    Jakob Rath 2021-04-6

--*/

#include "math/polysat/bit_constraint.h"

namespace polysat {

    std::ostream& bit_constraint::display(std::ostream& out) const {
            if (!m_value)
                out << "~";
            out << "v" << m_var << "[" << m_index << "] ";
        }
        return out;
    }

    bool bit_constraint::propagate(solver& s, pvar v) {       
        UNREACHABLE();
        return false;
    }

    constraint* bit_constraint::resolve(solver& s, pvar v) {
        UNREACHABLE();
        return nullptr;
    }

    bool bit_constraint::is_always_false() {
        return false;
    }

    bool bit_constraint::is_currently_false(solver& s) {
        return false;
    }

    void bit_constraint::narrow(solver& s) {
        bdd viable = s.m_bdd.mk_true();
        if (m_value)
            viable &= s.m_bdd.mk_var(m_index);
        else 
            viable &= s.m_bdd.mk_nvar(m_index);
        s.push_viable(v);
        s.m_viable[v] &= viable;
        if (s.m_viable[v].is_false()) 
            s.set_conflict(v);
    }

}
