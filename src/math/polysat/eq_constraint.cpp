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

    bool eq_constraint::is_always_false(bool is_positive) const {
        if (is_positive)
            return p().is_never_zero();
        else
            return p().is_zero();
    }

    bool eq_constraint::is_currently_false(solver& s, bool is_positive) const {
        pdd r = p().subst_val(s.assignment());
        if (is_positive)
            return r.is_never_zero();
        else
            return r.is_zero();
    }

    bool eq_constraint::is_currently_true(solver& s, bool is_positive) const {
        pdd r = p().subst_val(s.assignment());
        if (is_positive)
            return r.is_zero();
        else
            return r.is_never_zero();
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
