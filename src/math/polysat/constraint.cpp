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

    constraint* constraint::eq(unsigned lvl, bool_var bvar, csign_t sign, pdd const& p, p_dependency_ref const& d) {
        return alloc(eq_constraint, lvl, bvar, sign, p, d);
    }

    constraint* constraint::viable(unsigned lvl, bool_var bvar, csign_t sign, pvar v, bdd const& b, p_dependency_ref const& d) {
        return alloc(var_constraint, lvl, bvar, sign, v, b, d);
    }

    constraint* constraint::ule(unsigned lvl, bool_var bvar, csign_t sign, pdd const& a, pdd const& b, p_dependency_ref const& d) {
        return alloc(ule_constraint, lvl, bvar, sign, a, b, d);
    }

    constraint* constraint::ult(unsigned lvl, bool_var bvar, csign_t sign, pdd const& a, pdd const& b, p_dependency_ref const& d) {
        // a < b  <=>  !(b <= a)
        return ule(lvl, bvar, static_cast<csign_t>(!sign), b, a, d);
    }

    bool constraint::propagate(solver& s, pvar v) {
        LOG_H3("Propagate " << s.m_vars[v] << " in " << *this);
        SASSERT(!vars().empty());
        unsigned idx = 0;
        if (vars()[idx] != v)
            idx = 1;
        SASSERT(v == vars()[idx]);
        // find other watch variable.
        for (unsigned i = vars().size(); i-- > 2; ) {
            unsigned other_v = vars()[i];
            if (!s.is_assigned(other_v)) {
                s.add_watch(*this, other_v);
                std::swap(vars()[idx], vars()[i]);
                return true;
            }
        }
        // at most one variable remains unassigned.
        unsigned other_v = vars()[idx];
        propagate_core(s, v, other_v);
        return false;
    }

    void constraint::propagate_core(solver& s, pvar v, pvar other_v) {
        (void)v;
        (void)other_v;
        narrow(s);
    }

}
