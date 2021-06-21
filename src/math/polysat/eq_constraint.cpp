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
        out << p() << (sign() == pos_t ? " == 0" : " != 0");
        return display_extra(out);
    }

    constraint_ref eq_constraint::resolve(solver& s, pvar v) {
        if (is_positive())
            return eq_resolve(s, v);
        if (is_negative())
            return diseq_resolve(s, v);
        UNREACHABLE();
        return nullptr;
    }

    void eq_constraint::narrow(solver& s) {
        SASSERT(!is_undef());
        LOG("Assignment: " << assignments_pp(s));
        auto q = p().subst_val(s.assignment());
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
            s.push_cjust(v, this);

            rational a = q.hi().val();
            rational b = q.lo().val();
            s.m_vble.intersect_eq(a, v, b, is_positive());


            rational val;
            if (s.m_vble.find_viable(v, val) == dd::find_t::singleton) 
                s.propagate(v, val, *this);
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
        pdd r = p().subst_val(s.assignment());
        if (is_positive())
            return r.is_never_zero();
        if (is_negative())
            return r.is_zero();
        UNREACHABLE();
        return false;
    }

    bool eq_constraint::is_currently_true(solver& s) {
        pdd r = p().subst_val(s.assignment());
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

    constraint_ref eq_constraint::eq_resolve(solver& s, pvar v) {
        LOG("Resolve " << *this << " upon v" << v);
        if (s.m_conflict.size() != 1)
            return nullptr;
        if (!s.m_conflict.clauses().empty())
            return nullptr;
        constraint* c = s.m_conflict.units()[0];
        SASSERT(c->is_currently_false(s));
        // 'c == this' can happen if propagation was from decide() with only one value left
        // (e.g., if there's an unsatisfiable clause and we try all values).
        // Resolution would give us '0 == 0' in this case, which is useless.
        if (c == this)
            return nullptr;
        SASSERT(is_currently_true(s));  // TODO: might not always hold (due to similar case as in comment above?)
        if (c->is_eq() && c->is_positive()) {
            pdd a = c->to_eq().p();
            pdd b = p();
            pdd r = a;
            if (!a.resolve(v, b, r)) 
                return nullptr;
            p_dependency_ref d(s.m_dm.mk_join(c->dep(), dep()), s.m_dm);
            unsigned lvl = std::max(c->level(), level());
            return s.m_constraints.eq(lvl, pos_t, r, d);
        }
        return nullptr;
    }


    /**
     * Disequality constraints
     */

    constraint_ref eq_constraint::diseq_resolve(solver& s, pvar v) {
        NOT_IMPLEMENTED_YET();
        return nullptr;
    }



    /// Compute forbidden interval for equality constraint by considering it as p <=u 0 (or p >u 0 for disequality)
    bool eq_constraint::forbidden_interval(solver& s, pvar v, eval_interval& out_interval, constraint_ref& out_neg_cond)
    {
        SASSERT(!is_undef());

        // Current only works when degree(v) is at most one
        unsigned const deg = p().degree(v);
        if (deg > 1)
            return false;

        if (deg == 0) {
            return false;
            UNREACHABLE();  // this case is not useful for conflict resolution (but it could be handled in principle)
            // i is empty or full, condition would be this constraint itself?
            return true;
        }

        unsigned const sz = s.size(v);
        dd::pdd_manager& m = s.sz2pdd(sz);

        pdd p1 = m.zero();
        pdd e1 = m.zero();
        p().factor(v, 1, p1, e1);

        pdd e2 = m.zero();

        // Currently only works if coefficient is a power of two
        if (!p1.is_val())
            return false;
        rational a1 = p1.val();
        // TODO: to express the interval for coefficient 2^i symbolically, we need right-shift/upper-bits-extract in the language.
        // So currently we can only do it if the coefficient is 1.
        if (!a1.is_zero() && !a1.is_one())
            return false;
        /*
        unsigned j1 = 0;
        if (!a1.is_zero() && !a1.is_power_of_two(j1))
            return false;
        */

        // Concrete values of evaluable terms
        auto e1s = e1.subst_val(s.assignment());
        auto e2s = m.zero();
        SASSERT(e1s.is_val());
        SASSERT(e2s.is_val());

        // e1 + t <= 0, with t = 2^j1*y
        // condition for empty/full: 0 == -1, never satisfied, so we always have a proper interval!
        SASSERT(!a1.is_zero());
        pdd lo = 1 - e1;
        rational lo_val = (1 - e1s).val();
        pdd hi = -e1;
        rational hi_val = (-e1s).val();
        if (is_negative()) {
            swap(lo, hi);
            lo_val.swap(hi_val);
        }
        out_interval = eval_interval::proper(lo, lo_val, hi, hi_val);
        out_neg_cond = nullptr;
        return true;
    }

}
