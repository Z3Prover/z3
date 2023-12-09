/*++
Copyright (c) 2021 Microsoft Corporation

Module Name:

    polysat constraints

Author:

    Nikolaj Bjorner (nbjorner) 2021-03-19
    Jakob Rath 2021-04-06

--*/

#include "sat/smt/polysat/polysat_core.h"
#include "sat/smt/polysat/polysat_constraints.h"
#include "sat/smt/polysat/polysat_ule.h"
#include "sat/smt/polysat/polysat_umul_ovfl.h"

namespace polysat {

    signed_constraint constraints::ule(pdd const& p, pdd const& q) {
        pdd lhs = p, rhs = q;
        bool is_positive = true;
        ule_constraint::simplify(is_positive, lhs, rhs);
        auto* c = alloc(ule_constraint, p, q);
        m_trail.push(new_obj_trail(c));
        auto sc = signed_constraint(ckind_t::ule_t, c);
        return is_positive ? sc : ~sc;
    }

    signed_constraint constraints::umul_ovfl(pdd const& p, pdd const& q) { 
        auto* c = alloc(umul_ovfl_constraint, p, q);
        m_trail.push(new_obj_trail(c));
        return signed_constraint(ckind_t::umul_ovfl_t, c);
    }

    lbool signed_constraint::eval(assignment& a) const {
        lbool r = m_constraint->eval(a);
        return m_sign ? ~r : r;
    }

    std::ostream& signed_constraint::display(std::ostream& out) const {
        if (m_sign) out << "~";
        return out << *m_constraint;        
    }
}
