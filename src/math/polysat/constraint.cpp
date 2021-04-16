/*++
Copyright (c) 2021 Microsoft Corporation

Module Name:

    polysat constraints

Author:

    Nikolaj Bjorner (nbjorner) 2021-03-19
    Jakob Rath 2021-04-6

--*/

#include "math/polysat/constraint.h"
#include "math/polysat/solver.h"
#include "math/polysat/log.h"
#include "math/polysat/var_constraint.h"
#include "math/polysat/eq_constraint.h"
#include "math/polysat/ule_constraint.h"

namespace polysat {

    eq_constraint& constraint::to_eq() { 
        return *dynamic_cast<eq_constraint*>(this); 
    }

    eq_constraint const& constraint::to_eq() const { 
        return *dynamic_cast<eq_constraint const*>(this); 
    }

    constraint* constraint::eq(unsigned lvl, pdd const& p, p_dependency_ref& d) {
        return alloc(eq_constraint, lvl, p, d);
    }

    constraint* constraint::viable(unsigned lvl, pvar v, bdd const& b, p_dependency_ref& d) {
        return alloc(var_constraint, lvl, v, b, d);
    }

    constraint* constraint::ule(unsigned lvl, pdd const& a, pdd const& b, p_dependency_ref& d) {
        return alloc(ule_constraint, lvl, a, b, d);
    }

}
