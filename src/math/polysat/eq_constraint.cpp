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
        return out << p() << (sign() == pos_t ? " == 0" : " != 0") << " [" << m_status << "]";
    }

    constraint* eq_constraint::resolve(solver& s, pvar v) {
        if (is_positive())
            return eq_resolve(s, v);
        if (is_negative())
            return diseq_resolve(s, v);
        UNREACHABLE();
        return nullptr;
    }

    void eq_constraint::narrow(solver& s) {
        SASSERT(!is_undef());
        LOG("Assignment: " << s.m_search);
        auto q = p().subst_val(s.m_search);
        LOG("Substituted: " << p() << " := " << q);
        if (q.is_zero()) {
            if (is_positive())
                return;
            if (is_negative()) {
                LOG("Conflict (zero under current assignment)");
                s.set_conflict(*this);
                return;
            }
        }
        if (q.is_never_zero()) {
            if (is_positive()) {
                LOG("Conflict (never zero under current assignment)");
                s.set_conflict(*this);
                return;
            }
            if (is_negative())
                return;
        }

        if (q.is_unilinear()) {
            // a*x + b == 0
            pvar v = q.var();
            rational a = q.hi().val();
            rational b = q.lo().val();
            bddv const& x = s.var2bits(v).var();
            bddv lhs = a * x + b;
            rational zero = rational::zero();
            bdd xs = is_positive() ? (lhs == zero) : (lhs != zero);
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
        if (is_positive())
            return p().is_never_zero();
        if (is_negative())
            return p().is_zero();
        UNREACHABLE();
        return false;
    }

    bool eq_constraint::is_currently_false(solver& s) {
        pdd r = p().subst_val(s.m_search);
        if (is_positive())
            return r.is_never_zero();
        if (is_negative())
            return r.is_zero();
        UNREACHABLE();
        return false;
    }

    bool eq_constraint::is_currently_true(solver& s) {
        pdd r = p().subst_val(s.m_search);
        if (is_positive())
            return r.is_zero();
        if (is_negative())
            return r.is_never_zero();
        UNREACHABLE();
        return false;
    }

    /**
     * Equality constraints
     */

    constraint* eq_constraint::eq_resolve(solver& s, pvar v) {
        SASSERT(is_currently_true(s));
        if (s.m_conflict.size() != 1)
            return nullptr;
        constraint* c = s.m_conflict[0];
        SASSERT(c->is_currently_false(s));
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




    /**
     * Disequality constraints
     */

    constraint* eq_constraint::diseq_resolve(solver& s, pvar v) {
        NOT_IMPLEMENTED_YET();
        return nullptr;
    }

}
