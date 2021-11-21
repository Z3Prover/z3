/*++
Copyright (c) 2021 Microsoft Corporation

Module Name:

    polysat unsigned <= constraints

Author:

    Nikolaj Bjorner (nbjorner) 2021-03-19
    Jakob Rath 2021-04-6

Notes:

   Rewrite rules to simplify expressions.
   In the following let k, k1, k2 be values.
  
   - k1 <= k2   ==> 0 <= 0 if k1 <= k2
   - k1 <= k2   ==> 1 <= 0 if k1 >  k2
   - 0 <= p     ==> 0 <= 0
   - p <= -1    ==> 0 <= 0
   - k*2^n*p <= 0   ==> 2^n*p <= 0 if k is odd, leading coeffient is always a power of 2.
   - k <= p     ==> p - k <= - k - 1

TODO: clause simplifications:

   - p + k <= p  ==> p + k <= k & p != 0   for k != 0  
   - p*q = 0     ==> p = 0 or q = 0        applies to any factoring
   - 2*p <= 2*q  ==> (p >= 2^n-1 & q < 2^n-1) or (p >= 2^n-1 = q >= 2^n-1 & p <= q)
                 ==> (p >= 2^n-1 => q < 2^n-1 or p <= q) &
                     (p < 2^n-1 => p <= q) &
                     (p < 2^n-1 => q < 2^n-1)

   - 3*p <= 3*q ==> ?

Note:
     case p <= p + k is already covered because we test (lhs - rhs).is_val()
      
     It can be seen as an instance of lemma 5.2 of Supratik and John.

--*/

#include "math/polysat/constraint.h"
#include "math/polysat/solver.h"
#include "math/polysat/log.h"

namespace polysat {

    ule_constraint::ule_constraint(constraint_manager& m, pdd const& l, pdd const& r) :
        constraint(m, ckind_t::ule_t), m_lhs(l), m_rhs(r) {

        simplify();

        m_vars.append(m_lhs.free_vars());
        for (auto v : m_rhs.free_vars())
            if (!m_vars.contains(v))
                m_vars.push_back(v);

    }

    void ule_constraint::simplify() {
        if (m_lhs.is_zero()) {
            m_rhs = 0;
            return;
        }
        if (m_rhs.is_val() && m_rhs.val() == m_rhs.manager().max_value()) {
            m_lhs = 0, m_rhs = 0;
            return;
        }
        if (m_lhs == m_rhs) {
            m_lhs = m_rhs = 0;
            return;
        }
        if (m_lhs.is_val() && m_rhs.is_val()) {
            if (m_lhs.val() <= m_rhs.val())
                m_lhs = m_rhs = 0;
            else
                m_lhs = 1, m_rhs = 0;
            return;
        }
        // k <= p => p - k <= - k - 1
        if (m_lhs.is_val() && false) {
            pdd k = m_lhs;
            m_lhs = m_rhs - k;
            m_rhs = - k - 1;
        }
        // normalize leading coefficient to be a power of 2
        if (m_rhs.is_zero() && !m_lhs.leading_coefficient().is_power_of_two()) {
            rational lc = m_lhs.leading_coefficient();
            rational x, y;
            gcd(lc, m_lhs.manager().two_to_N(), x, y);
            if (x.is_neg())
                x = mod(x, m_lhs.manager().two_to_N());
            m_lhs *= x;
            SASSERT(m_lhs.leading_coefficient().is_power_of_two());
        }
    }

    std::ostream& ule_constraint::display(std::ostream& out, lbool status) const {
        out << m_lhs;
        if (is_eq() && status == l_true) out << " == ";
        else if (is_eq() && status == l_false) out << " != ";
        else if (status == l_true) out << " <= ";
        else if (status == l_false) out << " > ";
        else out << " <=/> ";
        return out << m_rhs;
    }

    std::ostream& ule_constraint::display(std::ostream& out) const {
        return out << m_lhs << (is_eq() ? " == " : " <= ") << m_rhs;
    }

    void ule_constraint::narrow(solver& s, bool is_positive) {
        auto p = lhs().subst_val(s.assignment());
        auto q = rhs().subst_val(s.assignment());

        LOG_H3("Narrowing " << *this);
        LOG("Assignment: " << assignments_pp(s));
        LOG("Substituted LHS: " << lhs() << " := " << p);
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

#if NEW_VIABLE
        // setup with viable2:
        // we no longer need cjust
        pvar v = null_var;
        if (p.is_unilinear())
            v = p.var();
        else if (q.is_unilinear())
            v = q.var();
        if (v != null_var) {
            signed_constraint sc(this, is_positive);
            s.m_viable.intersect(v, sc);
            rational val;
            switch (s.m_viable.find_viable(v, val)) {
            case dd::find_t::singleton:
                s.propagate(v, val, sc);
                break;
            case dd::find_t::empty:
                s.set_conflict(v);
                break;
            default:
                break;
            }                
        }
#else

        // p <= 0, e.g., p == 0
        if (q.is_zero() && p.is_unilinear()) {
            // a*x + b == 0
            pvar v = p.var();
            s.push_cjust(v, { this, is_positive });

            rational a = p.hi().val();
            rational b = p.lo().val();
            s.m_viable.intersect_eq(a, v, b, is_positive);

            rational val;
            if (s.m_viable.find_viable(v, val) == dd::find_t::singleton)
                s.propagate(v, val, { this, is_positive });
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
#endif
    }

    bool ule_constraint::is_always_false(bool is_positive, pdd const& lhs, pdd const& rhs) const {
        // TODO: other conditions (e.g. when forbidden interval would be full)
        if (is_positive) {
            if (rhs.is_zero())
                return lhs.is_never_zero();
            return lhs.is_val() && rhs.is_val() && lhs.val() > rhs.val();
        }
        else {
            if (lhs.is_zero())
                return true;  // 0 > ... is always false
            return (lhs.is_val() && rhs.is_val() && lhs.val() <= rhs.val()) || (lhs == rhs);
        }
    }

    bool ule_constraint::is_always_false(bool is_positive) const {
        return is_always_false(is_positive, lhs(), rhs());
    }

    bool ule_constraint::is_currently_false(assignment_t const& a, bool is_positive) const {
        auto p = lhs().subst_val(a);
        auto q = rhs().subst_val(a);
        return is_always_false(is_positive, p, q);
    }

    bool ule_constraint::is_currently_true(assignment_t const& a, bool is_positive) const {
        auto p = lhs().subst_val(a);
        auto q = rhs().subst_val(a);
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
