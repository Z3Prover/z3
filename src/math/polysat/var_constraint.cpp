/*++
Copyright (c) 2021 Microsoft Corporation

Module Name:

    polysat var_constraint

Author:

    Nikolaj Bjorner (nbjorner) 2021-03-19
    Jakob Rath 2021-04-6

--*/

#if 0
#include "math/polysat/var_constraint.h"
#include "math/polysat/solver.h"

namespace polysat {

    std::ostream& var_constraint::display(std::ostream& out) const {
        out << "v" << m_var << ": " << m_viable << "\n";
        return display_extra(out);
    }

    constraint_ref var_constraint::resolve(solver& s, pvar v) {
        UNREACHABLE();
        return nullptr;
    }

    bool var_constraint::is_always_false() {
        return false;
    }

    bool var_constraint::is_currently_false(solver& s) {
        return s.m_vble.is_false(m_var);
    }

    bool var_constraint::is_currently_true(solver& s) {
        return !is_currently_false(s);
    }

    void var_constraint::narrow(solver& s) {
        s.m_vble.intersect_viable(m_var, m_viable);
    }

}
#endif
