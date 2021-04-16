/*++
Copyright (c) 2021 Microsoft Corporation

Module Name:

    polysat eq_constraints

Author:

    Nikolaj Bjorner (nbjorner) 2021-03-19
    Jakob Rath 2021-04-6

--*/

#include "math/polysat/constraint.h"
#include "math/polysat/solver.h"
#include "math/polysat/log.h"

namespace polysat {

    std::ostream& eq_constraint::display(std::ostream& out) const {
        return out << p() << " == 0";
    }

    bool eq_constraint::propagate(solver& s, pvar v) {
        LOG_H3("Propagate " << s.m_vars[v] << " in " << *this);
        SASSERT(!vars().empty());
        unsigned idx = 0;
        if (vars()[idx] != v)
            idx = 1;
        SASSERT(v == vars()[idx]);
        // find other watch variable.
        for (unsigned i = vars().size(); i-- > 2; ) {
            if (!s.is_assigned(vars()[i])) {
                std::swap(vars()[idx], vars()[i]);
                return true;
            }
        }        

        LOG("Assignments: " << s.m_search);
        auto q = p().subst_val(s.m_search);
        LOG("Substituted: " << p() << " := " << q);
        TRACE("polysat", tout << p() << " := " << q << "\n";);
        if (q.is_zero()) 
            return false;
        if (q.is_never_zero()) {
            LOG("Conflict (never zero under current assignment)");
            s.set_conflict(*this);
            return false;
        }

        // at most one variable remains unassigned.
        auto other_var = vars()[1 - idx];
        SASSERT(!q.is_val() && q.var() == other_var);

        // Detect and apply unit propagation.
        if (try_narrow_with(q, s)) {
            rational val;
            switch (s.find_viable(other_var, val)) {
            case dd::find_int_t::empty:
                s.set_conflict(*this);
                return false;
            case dd::find_int_t::singleton:
                s.propagate(other_var, val, *this);
                return false;
            case dd::find_int_t::multiple:
                /* do nothing */
                break;
            }
        }

        return false;
    }

    constraint* eq_constraint::resolve(solver& s, pvar v) {
        if (s.m_conflict.size() != 1)
            return nullptr;
        constraint* c = s.m_conflict[0];
        if (c->is_eq()) {
            pdd a = c->to_eq().p();
            pdd b = p();
            pdd r = a;
            if (!a.resolve(v, b, r)) 
                return nullptr;
            p_dependency_ref d(s.m_dm.mk_join(c->dep(), dep()), s.m_dm);
            unsigned lvl = std::max(c->level(), level());
            return constraint::eq(lvl, r, d);             
        }
        return nullptr;
    }

    bool eq_constraint::try_narrow_with(pdd const& q, solver& s) {
        if (q.is_linear() && q.free_vars().size() == 1) {
            // a*x + b == 0
            pvar v = q.var();
            rational a = q.hi().val();
            rational b = q.lo().val();
            bdd xs = s.m_bdd.mk_affine(a, b, s.size(v));
            s.intersect_viable(v, xs);
            s.push_cjust(v, this);
            return true;
        }
        // TODO: what other constraints can be extracted cheaply?
        return false;
    }

    void eq_constraint::narrow(solver& s) {
        // NSB code review:
        // This should also use the current assignment so be similar to propagate.
        // The idea is that narrow is invoked when the constraint is first added
        // and also when the constraint is used in a conflict.
        // When it is used in a conflict, there could be a partial assignment in s.m_search
        // that fixes variables in p().
        // 
        (void)try_narrow_with(p(), s);
    }

    bool eq_constraint::is_always_false() {
        return p().is_never_zero();
    }

    bool eq_constraint::is_currently_false(solver& s) {
        pdd r = p().subst_val(s.m_search);
        return r.is_never_zero();
    }

}
