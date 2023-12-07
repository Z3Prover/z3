/*++
Copyright (c) 2021 Microsoft Corporation

Module Name:

    polysat constraints

Author:

    Nikolaj Bjorner (nbjorner) 2021-03-19
    Jakob Rath 2021-04-06

--*/
#include "sat/smt/polysat_core.h"
#include "sat/smt/polysat_solver.h"
#include "sat/smt/polysat_constraints.h"

namespace polysat {

    signed_constraint constraints::ule(pdd const& p, pdd const& q) {
        auto* c = alloc(ule_constraint, p, q);
        m_trail.push(new_obj_trail(c));
        return signed_constraint(ckind_t::ule_t, c);
    }
}
