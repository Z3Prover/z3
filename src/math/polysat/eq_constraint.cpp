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

    std::ostream& eq_constraint::display(std::ostream& out, lbool status) const {
        out << p();
        if (status == l_true) out << " == 0";
        else if (status == l_false) out << " != 0";
        else out << " ==/!= 0";
        return display_extra(out, status);
    }

    void eq_constraint::narrow(solver& s, bool is_positive) {
        LOG("Assignment: " << assignments_pp(s));
        auto q = p().subst_val(s.assignment());
        LOG("Substituted: " << p() << " := " << q);
        if (q.is_zero()) {
            if (!is_positive) {
                LOG("Conflict (zero under current assignment)");
                s.set_conflict({this, is_positive});
            }
            return;
        }
        if (q.is_never_zero()) {
            if (is_positive) {
                LOG("Conflict (never zero under current assignment)");
                s.set_conflict({this, is_positive});
            }
            return;
        }

        if (q.is_unilinear()) {
            // a*x + b == 0
            pvar v = q.var();
            s.push_cjust(v, {this, is_positive});

            rational a = q.hi().val();
            rational b = q.lo().val();
            s.m_viable.intersect_eq(a, v, b, is_positive);


            rational val;
            if (s.m_viable.find_viable(v, val) == dd::find_t::singleton) 
                s.propagate(v, val, {this, is_positive});
            return;
        }

        // TODO: what other constraints can be extracted cheaply?
    }

    bool eq_constraint::is_always_false(bool is_positive) {
        if (is_positive)
            return p().is_never_zero();
        else
            return p().is_zero();
    }

    bool eq_constraint::is_currently_false(solver& s, bool is_positive) {
        pdd r = p().subst_val(s.assignment());
        if (is_positive)
            return r.is_never_zero();
        else
            return r.is_zero();
    }

    bool eq_constraint::is_currently_true(solver& s, bool is_positive) {
        pdd r = p().subst_val(s.assignment());
        if (is_positive)
            return r.is_zero();
        else
            return r.is_never_zero();
    }


    /**
     * Equality constraints
     */

    // constraint_ref eq_constraint::eq_resolve(solver& s, pvar v) {
    //     LOG("Resolve " << *this << " upon v" << v);
    //     if (s.m_conflict.size() != 1)
    //         return nullptr;
    //     if (!s.m_conflict.clauses().empty())
    //         return nullptr;
    //     constraint* c = s.m_conflict.units()[0];
    //     SASSERT(c->is_currently_false(s));
    //     // 'c == this' can happen if propagation was from decide() with only one value left
    //     // (e.g., if there's an unsatisfiable clause and we try all values).
    //     // Resolution would give us '0 == 0' in this case, which is useless.
    //     if (c == this)
    //         return nullptr;
    //     SASSERT(is_currently_true(s));  // TODO: might not always hold (due to similar case as in comment above?)
    //     if (c->is_eq() && c->is_positive()) {
    //         pdd a = c->to_eq().p();
    //         pdd b = p();
    //         pdd r = a;
    //         if (!a.resolve(v, b, r)) 
    //             return nullptr;
    //         p_dependency_ref d(s.m_dm.mk_join(c->dep(), dep()), s.m_dm);
    //         unsigned lvl = std::max(c->level(), level());
    //         return s.m_constraints.eq(lvl, pos_t, r, d);
    //     }
    //     return nullptr;
    // }


    /// Compute forbidden interval for equality constraint by considering it as p <=u 0 (or p >u 0 for disequality)
    bool eq_constraint::forbidden_interval(solver& s, bool is_positive, pvar v, eval_interval& out_interval, scoped_signed_constraint& out_neg_cond)
    {
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
        if (!e1s.is_val())
            return false;
        SASSERT(e1s.is_val());

        // e1 + t <= 0, with t = 2^j1*y
        // condition for empty/full: 0 == -1, never satisfied, so we always have a proper interval!
        SASSERT(!a1.is_zero());
        pdd lo = 1 - e1;
        rational lo_val = (1 - e1s).val();
        pdd hi = -e1;
        rational hi_val = (-e1s).val();
        if (!is_positive) {
            swap(lo, hi);
            lo_val.swap(hi_val);
        }
        out_interval = eval_interval::proper(lo, lo_val, hi, hi_val);
        out_neg_cond = nullptr;
        return true;
    }

    inequality eq_constraint::as_inequality(bool is_positive) const {
        pdd zero = p() - p();
        if (is_positive)
            // p <= 0
            return inequality(p(), zero, false, this);
        else 
            // 0 < p
            return inequality(zero, p(), true, this);
    }

    unsigned eq_constraint::hash() const {
    	return p().hash();
    }
    
    bool eq_constraint::operator==(constraint const& other) const {
    	return other.is_eq() && p() == other.to_eq().p();
    }
 
}
