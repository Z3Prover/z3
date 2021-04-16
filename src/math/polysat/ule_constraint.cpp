/*++
Copyright (c) 2021 Microsoft Corporation

Module Name:

    polysat ule_constraints

Author:

    Nikolaj Bjorner (nbjorner) 2021-03-19
    Jakob Rath 2021-04-6

--*/

#include "math/polysat/constraint.h"
#include "math/polysat/solver.h"

namespace polysat {

    std::ostream& ule_constraint::display(std::ostream& out) const {
        return out << m_lhs << " <=u " << m_rhs;
    }

    bool ule_constraint::propagate(solver& s, pvar v) {
        return false;
    }

    constraint* ule_constraint::resolve(solver& s, pvar v) {
        return nullptr;
    }

    void ule_constraint::narrow(solver& s) {
    }

    bool ule_constraint::is_always_false() {
        return false;
    }

    bool ule_constraint::is_currently_false(solver& s) {
        return false;
    }

}
