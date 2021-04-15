/*++
Copyright (c) 2021 Microsoft Corporation

Module Name:

    polysat constraints

Author:

    Nikolaj Bjorner (nbjorner) 2021-03-19

--*/

#include "math/polysat/constraint.h"

namespace polysat {


    constraint* constraint::eq(unsigned lvl, pdd const& p, p_dependency_ref& d) {
        return alloc(eq_constraint, lvl, p, dep);
    }

    std::ostream& constraint::display(std::ostream& out) const {
        return out << p() << " == 0";
    }

}
