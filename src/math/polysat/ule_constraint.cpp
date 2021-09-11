/*++
Copyright (c) 2021 Microsoft Corporation

Module Name:

    polysat unsigned <= constraints

Author:

    Nikolaj Bjorner (nbjorner) 2021-03-19
    Jakob Rath 2021-04-6

--*/

#include "math/polysat/constraint.h"
#include "math/polysat/solver.h"
#include "math/polysat/log.h"

namespace polysat {

    std::ostream& ule_constraint::display(std::ostream& out, lbool status) const {
        out << m_lhs;
        if (status == l_true) out << " <= ";
        else if (status == l_false) out << " > ";
        else out << " <=/> ";
        out << m_rhs;
        return display_extra(out, status);
    }

    void ule_constraint::narrow(solver& s, bool is_positive) {
        LOG_H3("Narrowing " << *this);
        LOG("Assignment: " << assignments_pp(s));
        auto p = lhs().subst_val(s.assignment());
        LOG("Substituted LHS: " << lhs() << " := " << p);
        auto q = rhs().subst_val(s.assignment());
        LOG("Substituted RHS: " << rhs() << " := " << q);

        if (is_always_false(is_positive, p, q)) {
            s.set_conflict({this, is_positive});
            return;
        }
        if (p.is_val() && q.is_val()) {
            SASSERT(!is_positive || p.val() <= q.val());
            SASSERT(is_positive || p.val() > q.val());
            return;
        }

        pvar v = null_var;
        rational a, b, c, d;
        if (p.is_unilinear() && q.is_unilinear() && p.var() == q.var()) {
            // a*x + b <=u c*x + d
            v = p.var();
            a = p.hi().val();
            b = p.lo().val();
            c = q.hi().val();
            d = q.lo().val();
        }
        else if (p.is_unilinear() && q.is_val()) {
            // a*x + b <=u d
            v = p.var();
            a = p.hi().val();
            b = p.lo().val();
            c = rational::zero();
            d = q.val();
        }
        else if (p.is_val() && q.is_unilinear()) {
            // b <=u c*x + d
            v = q.var();
            a = rational::zero();
            b = p.val();
            c = q.hi().val();
            d = q.lo().val();
        }
        if (v != null_var) {
            s.push_cjust(v, {this, is_positive});

            s.m_viable.intersect_ule(v, a, b, c, d, is_positive);

            rational val;
            if (s.m_viable.find_viable(v, val) == dd::find_t::singleton) 
                s.propagate(v, val, {this, is_positive});

            return;
        }

        // TODO: other cheap constraints possible?
    }

    bool ule_constraint::is_always_false(bool is_positive, pdd const& lhs, pdd const& rhs) const {
        // TODO: other conditions (e.g. when forbidden interval would be full)
        if (is_positive)
            return lhs.is_val() && rhs.is_val() && lhs.val() > rhs.val();
        else {
            if (lhs.is_zero())
                return true;  // 0 > ... is always false
            return (lhs.is_val() && rhs.is_val() && lhs.val() <= rhs.val()) || (lhs == rhs);
        }
    }

    bool ule_constraint::is_always_false(bool is_positive) const {
        return is_always_false(is_positive, lhs(), rhs());
    }

    bool ule_constraint::is_currently_false(solver& s, bool is_positive) const {
        auto p = lhs().subst_val(s.assignment());
        auto q = rhs().subst_val(s.assignment());
        return is_always_false(is_positive, p, q);
    }

    bool ule_constraint::is_currently_true(solver& s, bool is_positive) const {
        auto p = lhs().subst_val(s.assignment());
        auto q = rhs().subst_val(s.assignment());
        if (is_positive) {
            if (p.is_zero())
                return true;
            return p.is_val() && q.is_val() && p.val() <= q.val();
        }
        else 
            return p.is_val() && q.is_val() && p.val() > q.val();
    }

    inequality ule_constraint::as_inequality(bool is_positive) const {
        if (is_positive)
            return inequality(lhs(), rhs(), false, this);
        else 
            return inequality(rhs(), lhs(), true, this);
    }

    unsigned ule_constraint::hash() const {
    	return mk_mix(lhs().hash(), rhs().hash(), 23);
    }
    
    bool ule_constraint::operator==(constraint const& other) const {
        return other.is_ule() && lhs() == other.to_ule().lhs() && rhs() == other.to_ule().rhs();
    }

}
