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
        // at most one variable remains unassigned.

        narrow(s);
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
            constraint* lemma = constraint::eq(lvl, s.m_next_bvar++, pos_t, r, d);
            lemma->assign_eh(true);
            return lemma;
        }
        return nullptr;
    }

    void eq_constraint::narrow(solver& s) {
        LOG("Assignment: " << s.m_search);
        auto q = p().subst_val(s.m_search);
        LOG("Substituted: " << p() << " := " << q);
        if (q.is_zero())
            return;
        if (q.is_never_zero()) {
            LOG("Conflict (never zero under current assignment)");
            s.set_conflict(*this);
            return;
        }

        if (q.is_unilinear()) {
            // a*x + b == 0
            pvar v = q.var();
            rational a = q.hi().val();
            rational b = q.lo().val();
            bddv const& x = s.var2bits(v).var();
            bdd xs = (a * x + b == rational(0));
            s.push_cjust(v, this);
            s.intersect_viable(v, xs);

            rational val;
            if (s.find_viable(v, val) == dd::find_t::singleton) {
                s.propagate(v, val, *this);
            }

            return;
        }

        // TODO: what other constraints can be extracted cheaply?
    }

    bool eq_constraint::is_always_false() {
        return p().is_never_zero();
    }

    bool eq_constraint::is_currently_false(solver& s) {
        pdd r = p().subst_val(s.m_search);
        return r.is_never_zero();
    }

}
