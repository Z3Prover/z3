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

    std::ostream& ule_constraint::display(std::ostream& out) const {
        return out << m_lhs << (sign() == pos_t ? " <=u " : " >u ") << m_rhs << " [" << m_status << "]";
    }

    bool ule_constraint::propagate(solver& s, pvar v) {
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

        narrow(s);
        return false;
    }

    constraint* ule_constraint::resolve(solver& s, pvar v) {
        return nullptr;
    }

    void ule_constraint::narrow(solver& s) {
        LOG("Assignment: " << s.m_search);
        auto p = lhs().subst_val(s.m_search);
        LOG("Substituted LHS: " << lhs() << " := " << p);
        auto q = rhs().subst_val(s.m_search);
        LOG("Substituted RHS: " << rhs() << " := " << q);

        if (is_always_false(p, q)) {
            s.set_conflict(*this);
            return;
        }
        if (p.is_val() && q.is_val()) {
            SASSERT(!is_positive() || p.val() <= q.val());
            SASSERT(!is_negative() || p.val() > q.val());
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
            bddv const& x = s.var2bits(v).var();
            bddv l = a * x + b;
            bddv r = c * x + d;
            bdd xs = is_positive() ? (l <= r) : (l > r);
            s.push_cjust(v, this);
            s.intersect_viable(v, xs);

            rational val;
            if (s.find_viable(v, val) == dd::find_t::singleton) {
                s.propagate(v, val, *this);
            }

            return;
        }

        // TODO: other cheap constraints possible?
    }

    bool ule_constraint::is_always_false(pdd const& lhs, pdd const& rhs) {
        // TODO: other conditions (e.g. when forbidden interval would be full)
        VERIFY(!is_undef());
        if (is_positive())
            return lhs.is_val() && rhs.is_val() && lhs.val() > rhs.val();
        else 
            return lhs.is_val() && rhs.is_val() && lhs.val() <= rhs.val();
    }

    bool ule_constraint::is_always_false() {
        return is_always_false(lhs(), rhs());
    }

    bool ule_constraint::is_currently_false(solver& s) {
        auto p = lhs().subst_val(s.m_search);
        auto q = rhs().subst_val(s.m_search);
        return is_always_false(p, q);
    }

    bool ule_constraint::is_currently_true(solver& s) {
        auto p = lhs().subst_val(s.m_search);
        auto q = rhs().subst_val(s.m_search);
        VERIFY(!is_undef());
        if (is_positive())
            return p.is_val() && q.is_val() && p.val() <= q.val();
        else 
            return p.is_val() && q.is_val() && p.val() > q.val();
    }

    /**
     * Precondition: all variables other than v are assigned.
     */
    bool ule_constraint::forbidden_interval(solver& s, pvar v, eval_interval& i, constraint*& neg_condition)
    {
        SASSERT(!is_undef());

        // Current only works when degree(v) is at most one on both sides
        unsigned const deg1 = lhs().degree(v);
        unsigned const deg2 = rhs().degree(v);
        if (deg1 > 1 || deg2 > 1)
            return false;

        if (deg1 == 0 && deg2 == 0) {
            UNREACHABLE();  // this case is not useful for conflict resolution (but it could be handled in principle)
            // i is empty or full, condition would be this constraint itself?
            return true;
        }

        unsigned const sz = s.size(v);
        dd::pdd_manager& m = s.sz2pdd(sz);

        pdd p1 = m.zero();
        pdd e1 = m.zero();
        if (deg1 == 0)
            e1 = lhs();
        else
            lhs().factor(v, 1, p1, e1);

        pdd p2 = m.zero();
        pdd e2 = m.zero();
        if (deg2 == 0)
            e2 = rhs();
        else
            rhs().factor(v, 1, p2, e2);

        // Interval extraction only works if v-coefficients are the same
        if (deg1 != 0 && deg2 != 0 && p1 != p2)
            return false;

        // Currently only works if coefficient is a power of two
        if (!p1.is_val())
            return false;
        if (!p2.is_val())
            return false;
        rational a1 = p1.val();
        rational a2 = p2.val();
        // TODO: to express the interval for coefficient 2^i symbolically, we need right-shift/upper-bits-extract in the language.
        // So currently we can only do it if the coefficient is 1.
        if (!a1.is_zero() && !a1.is_one())
            return false;
        if (!a2.is_zero() && !a2.is_one())
            return false;
        /*
        unsigned j1 = 0;
        unsigned j2 = 0;
        if (!a1.is_zero() && !a1.is_power_of_two(j1))
            return false;
        if (!a2.is_zero() && !a2.is_power_of_two(j2))
            return false;
        */

        // Concrete values of evaluable terms
        auto e1s = e1.subst_val(s.m_search);
        auto e2s = e2.subst_val(s.m_search);
        SASSERT(e1s.is_val());
        SASSERT(e2s.is_val());

        bool is_trivial;
        pdd condition_body = m.zero();
        pdd lo = m.zero();
        rational lo_val = rational::zero();
        pdd hi = m.zero();
        rational hi_val = rational::zero();

        if (a2.is_zero()) {
            SASSERT(!a1.is_zero());
            // e1 + t <= e2, with t = 2^j1*y
            // condition for empty/full: e2 == -1
            is_trivial = (e2s + 1).is_zero();
            condition_body = e2 + 1;
            if (!is_trivial) {
                lo = e2 - e1 + 1;
                lo_val = (e2s - e1s + 1).val();
                hi = -e1;
                hi_val = (-e1s).val();
            }
        }
        else if (a1.is_zero()) {
            SASSERT(!a2.is_zero());
            // e1 <= e2 + t, with t = 2^j2*y
            // condition for empty/full: e1 == 0
            is_trivial = e1s.is_zero();
            condition_body = e1;
            if (!is_trivial) {
                lo = -e2;
                lo_val = (-e2s).val();
                hi = e1 - e2;
                hi_val = (e1s - e2s).val();
            }
        }
        else {
            SASSERT(!a1.is_zero());
            SASSERT(!a2.is_zero());
            // e1 + t <= e2 + t, with t = 2^j1*y = 2^j2*y
            // condition for empty/full: e1 == e2
            is_trivial = e1s.val() == e2s.val();
            condition_body = e1 - e2;
            if (!is_trivial) {
                lo = -e2;
                lo_val = (-e2s).val();
                hi = -e1;
                hi_val = (-e1s).val();
            }
        }

        if (condition_body.is_val()) {
            // Condition is trivial; no need to create a constraint for that.
            SASSERT(is_trivial == condition_body.is_zero());
            neg_condition = nullptr;
        }
        else
            neg_condition = constraint::eq(level(), s.m_next_bvar++, is_trivial ? neg_t : pos_t, condition_body, m_dep);

        if (is_trivial) {
            if (is_positive())
                i = eval_interval::empty(m);
            else
                i = eval_interval::full();
        } else {
            if (is_negative()) {
                swap(lo, hi);
                lo_val.swap(hi_val);
            }
            i = eval_interval::proper(lo, lo_val, hi, hi_val);
        }

        return true;
    }

}
