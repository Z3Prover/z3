/*++
Copyright (c) 2021 Microsoft Corporation

Module Name:

    polysat unsigned <= constraints

Author:

    Nikolaj Bjorner (nbjorner) 2021-03-19
    Jakob Rath 2021-04-6

Notes:

   Canonical representation of equation p == 0 is the constraint p <= 0.
   The alternatives p < 1, -1 <= q, q > -2 are eliminated.

   Rewrite rules to simplify expressions.
   In the following let k, k1, k2 be values.

   - k1 <= k2       ==>   0 <= 0 if k1 <= k2
   - k1 <= k2       ==>   1 <= 0 if k1 >  k2
   - 0 <= p         ==>   0 <= 0
   - p <= 0         ==>   1 <= 0 if p is never zero due to parity
   - p <= -1        ==>   0 <= 0
   - k <= p         ==>   p - k <= - k - 1
   - k*2^n*p <= 0   ==>   2^n*p <= 0 if k is odd, leading coeffient is always a power of 2.

   Note: the rules will rewrite alternative formulations of equations:
   - -1 <= p        ==>   p + 1 <= 0
   -  1 <= p        ==>   p - 1 <= -2

   Rewrite rules on signed constraints:

   - p > -2         ==>   p + 1 <= 0
   - p <= -2        ==>   p + 1 > 0

   At this point, all equations are in canonical form.

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

The following forms are equivalent:

    p <= q
    p <= p - q - 1
    q - p <= q
    q - p <= -p - 1
    -q - 1 <= -p - 1
    -q - 1 <= p - q - 1

Useful lemmas:

    - p <= q    ==>   p == 0  ||  -q <= -p

--*/

#include "math/polysat/constraint.h"
#include "math/polysat/solver.h"
#include "math/polysat/log.h"

namespace {
    using namespace polysat;

    // Simplify lhs <= rhs.
    //
    // NOTE: the result should not depend on the initial value of is_positive;
    //       the purpose of is_positive is to allow flipping the sign as part of a rewrite rule.
    void simplify_impl(bool& is_positive, pdd& lhs, pdd& rhs) {
        // 0 <= p   -->   0 <= 0
        if (lhs.is_zero()) {
            rhs = 0;
            return;
        }
        // p <= -1   -->   0 <= 0
        if (rhs.is_max()) {
            lhs = 0, rhs = 0;
            return;
        }
        // p <= p   -->   0 <= 0
        if (lhs == rhs) {
            lhs = 0, rhs = 0;
            return;
        }
        // Evaluate constants
        if (lhs.is_val() && rhs.is_val()) {
            if (lhs.val() <= rhs.val())
                lhs = 0, rhs = 0;
            else
                lhs = 0, rhs = 0, is_positive = !is_positive;
            return;
        }

#if 0
        // TODO: maybe enable this later to make some constraints more "readable"
        // p - k <= -k - 1  -->  k <= p
        if (rhs.is_val() && !rhs.is_zero() && lhs.offset() == (rhs + 1).val()) {
            // LOG("Simplifying    " << lhs << " <= " << rhs);
            std::abort();
            pdd k = -(rhs + 1);
            rhs = lhs + k;
            lhs = k;
            // LOG("       into    " << lhs << " <= " << rhs);
        }
#endif

        // -1 <= p  -->   p + 1 <= 0
        if (lhs.is_max()) {
            lhs = rhs + 1;
            rhs = 0;
        }

        // 1 <= p   -->   p > 0
        if (lhs.is_one()) {
            lhs = rhs;
            rhs = 0;
            is_positive = !is_positive;
        }

#if 0
        // TODO: enabling this rule leads to unsoundness in 1041-minimized (but the rule itself is correct)
        // k <= p   -->   p - k <= - k - 1
        if (lhs.is_val()) {
            pdd k = lhs;
            lhs = rhs - k;
            rhs = - k - 1;
        }
#endif

        // p + 1 <= p  -->  p + 1 <= 0
        // p <= p - 1  -->  p <= 0
        //
        // p + k <= p       -->  p + k <= k - 1
        // p     <= p - k   -->  p     <= k - 1
        // TODO: subsumed by next condition
        if ((lhs - rhs).is_val()) {
            pdd k = lhs - rhs;
            rhs = k - 1;
        }

        // Try to reduce the number of variables on one side using one of these rules:
        //
        //      p <= q  -->  p <= p - q - 1
        //      p <= q  -->  q - p <= q
        //
        // Possible alternative to 1:
        //      p <= q  -->  q - p <= -p - 1
        // Possible alternative to 2:
        //      p <= q  -->  -q-1 <= p - q - 1
        //
        // Example:
        //
        //      x <= x + y  -->  x <= - y - 1
        //      x + y <= x  -->  -y <= x
        if (false && !lhs.is_val() && !rhs.is_val()) {
            // TODO: disabled because it kills bench31 (by rewriting just a single constraint...)
            unsigned const lhs_vars = lhs.free_vars().size();
            unsigned const rhs_vars = rhs.free_vars().size();
            unsigned const diff_vars = (lhs - rhs).free_vars().size();
            if (diff_vars < lhs_vars || diff_vars < rhs_vars) {
                verbose_stream() << "IN:  " << ule_pp(to_lbool(is_positive), lhs, rhs) << "\n";
                if (lhs_vars <= rhs_vars)
                    rhs = lhs - rhs - 1;
                else
                    lhs = rhs - lhs;
                verbose_stream() << "OUT: " << ule_pp(to_lbool(is_positive), lhs, rhs) << "\n";
            }
        }

        // p >  -2   -->   p + 1 <= 0
        // p <= -2   -->   p + 1 >  0
        if (rhs.is_val() && !rhs.is_zero() && (rhs + 2).is_zero()) {
            // Note: rhs.is_zero() iff rhs.manager().power_of_2() == 1 (the rewrite is not wrong for M=2, but useless)
            lhs = lhs + 1;
            rhs = 0;
            is_positive = !is_positive;
        }
        // 2p + 1 <= 0   -->   0 < 0
        if (rhs.is_zero() && lhs.is_never_zero()) {
            lhs = 0;
            is_positive = !is_positive;
            return;
        }
        // a*p + q <= 0   -->   p + a^-1*q <= 0   for a odd
        if (rhs.is_zero() && !lhs.leading_coefficient().is_power_of_two()) {
            rational lc = lhs.leading_coefficient();
            rational x, y;
            gcd(lc, lhs.manager().two_to_N(), x, y);
            if (x.is_neg())
                x = mod(x, lhs.manager().two_to_N());
            lhs *= x;
            SASSERT(lhs.leading_coefficient().is_power_of_two());
        }
    } // simplify_impl
}


namespace polysat {

    ule_constraint::ule_constraint(pdd const& l, pdd const& r) :
        constraint(ckind_t::ule_t), m_lhs(l), m_rhs(r) {

        m_vars.append(m_lhs.free_vars());
        for (auto v : m_rhs.free_vars())
            if (!m_vars.contains(v))
                m_vars.push_back(v);
    }

    void ule_constraint::simplify(bool& is_positive, pdd& lhs, pdd& rhs) {
#ifndef NDEBUG
        bool const old_is_positive = is_positive;
        pdd const old_lhs = lhs;
        pdd const old_rhs = rhs;
#endif
        simplify_impl(is_positive, lhs, rhs);
#ifndef NDEBUG
        if (old_is_positive != is_positive || old_lhs != lhs || old_rhs != rhs) {
            ule_pp const old_ule(to_lbool(old_is_positive), old_lhs, old_rhs);
            ule_pp const new_ule(to_lbool(is_positive), lhs, rhs);
            LOG("Simplify: " << old_ule << "   -->   " << new_ule);
            // always-false and always-true constraints should be rewritten to 0 != 0 and 0 == 0, respectively.
            if (is_always_false(old_is_positive, old_lhs, old_rhs)) {
                SASSERT(!is_positive);
                SASSERT(lhs.is_zero());
                SASSERT(rhs.is_zero());
            }
            if (is_always_true(old_is_positive, old_lhs, old_rhs)) {
                SASSERT(is_positive);
                SASSERT(lhs.is_zero());
                SASSERT(rhs.is_zero());
            }
        }
#endif
    }

    std::ostream& ule_constraint::display(std::ostream& out, lbool status, pdd const& lhs, pdd const& rhs) {
        out << lhs;
        if (rhs.is_zero() && status == l_true) out << " == ";
        else if (rhs.is_zero() && status == l_false) out << " != ";
        else if (status == l_true) out << " <= ";
        else if (status == l_false) out << " > ";
        else out << " <=/> ";
        return out << rhs;
    }

    std::ostream& ule_constraint::display(std::ostream& out, lbool status) const {
        return display(out, status, m_lhs, m_rhs);
    }

    std::ostream& ule_constraint::display(std::ostream& out) const {
        return display(out, l_true, m_lhs, m_rhs);
    }

    void ule_constraint::narrow(solver& s, bool is_positive, bool first) {
        auto p = s.subst(lhs());
        auto q = s.subst(rhs());

        signed_constraint sc(this, is_positive);

        LOG_H3("Narrowing " << sc);
        LOG_V(10, "Assignment: " << assignments_pp(s));
        LOG_V(10, "Substituted LHS: " << lhs() << " := " << p);
        LOG_V(10, "Substituted RHS: " << rhs() << " := " << q);

        if (is_always_false(is_positive, p, q)) {
            s.set_conflict(sc);
            return;
        }
        if (p.is_val() && q.is_val()) {
            SASSERT(!is_positive || p.val() <= q.val());
            SASSERT(is_positive || p.val() > q.val());
            return;
        }

        s.m_viable.intersect(p, q, sc);

        if (first && !is_positive && !lhs().is_val() && !rhs().is_val()) {
            // lhs > rhs  ==>  -1 > rhs
            s.add_clause(~sc, s.ult(rhs(), -1), false);
            // lhs > rhs  ==>  lhs > 0
            s.add_clause(~sc, s.ult(0, lhs()), false);
        }

#if 0
        propagate_bits(s, is_positive);
#endif
    }

    // Evaluate lhs <= rhs
    lbool ule_constraint::eval(pdd const& lhs, pdd const& rhs) {
        // NOTE: don't assume simplifications here because we also call this on partially substituted constraints
        if (lhs.is_zero())
            return l_true;      // 0 <= p
        if (lhs == rhs)
            return l_true;      // p <= p
        if (rhs.is_max())
            return l_true;      // p <= -1
        if (rhs.is_zero() && lhs.is_never_zero())
            return l_false;     // p <= 0 implies p == 0
        if (lhs.is_one() && rhs.is_never_zero())
            return l_true;      // 1 <= p implies p != 0
        if (lhs.is_val() && rhs.is_val())
            return to_lbool(lhs.val() <= rhs.val());
        return l_undef;
   }

    lbool ule_constraint::eval() const {
        return eval(lhs(), rhs());
    }

    lbool ule_constraint::eval(assignment const& a) const {
        return eval(a.apply_to(lhs()), a.apply_to(rhs()));
    }
    
    bool ule_constraint::propagate_bits(solver& s, bool is_positive) {
        if (is_eq() && is_positive) {
            vector<optional<pdd>> e;
            bool failed = false;
            for (const auto& m : lhs()) {
                if (e.size() > 1) {
                    failed = true;
                    break;
                }
                pdd p = lhs().manager().mk_val(m.coeff);
                for (pvar v : m.vars)
                    p *= s.var(v);
                e.push_back(optional(p));
                if (e.size() == 2 && (m.coeff < 0 || m.coeff >= rational::power_of_two(p.power_of_2() - 1)))
                    std::swap(e[0], e[1]); // try to keep it positive
            }
            if (!failed && !e.empty()) {
                if (e.size() == 1)
                    e.push_back(optional(lhs().manager().mk_val(0)));
                else
                    e[0] = optional(-*(e[0]));
                SASSERT(e.size() == 2);
                const tbv_ref& lhs_val = *s.m_fixed_bits.eval(s, *(e[0]));
                const tbv_ref& rhs_val = *s.m_fixed_bits.eval(s, *(e[1]));
                LOG("Bit-Propagating: " << lhs_val << " = " << rhs_val);
                unsigned sz = lhs_val.num_tbits();
                for (unsigned i = 0; i < sz; i++) {
                    // we propagate in both directions to get the least decision level
                    if (lhs_val[i] != BIT_z) {
                        if (!s.m_fixed_bits.fix_bit(s, *(e[1]), i, lhs_val[i], bit_justification_constraint::mk_unary(s, this, { *(e[0]), i }), true))
                            return false;
                    }
                    if (rhs_val[i] != BIT_z) {
                         if (!s.m_fixed_bits.fix_bit(s, *(e[0]), i, rhs_val[i], bit_justification_constraint::mk_unary(s, this, { *(e[1]), i }), true))
                             return false;
                    }
                }
                return true;
            }
        }
        
        pdd lhs = is_positive ? m_lhs : m_rhs;
        pdd rhs = is_positive ? m_rhs : m_lhs;
        
        const tbv_ref& lhs_val = *s.m_fixed_bits.eval(s, lhs);
        const tbv_ref& rhs_val = *s.m_fixed_bits.eval(s, rhs);
        unsigned sz = lhs_val.num_tbits();
        
        LOG("Bit-Propagating: " << lhs << " (" << lhs_val << ") " << (is_positive ? "<= " :  "< ") << rhs << " (" << rhs_val << ")");
        
        // TODO: Propagate powers of 2 (lower bound)
        bool conflict = false;
        bit_dependencies dep;
        static unsigned char action_lookup[] = {
            // lhs <= rhs
            // 0 .. break; could be still satisfied; 
            // 1 ... continue; there might still be a conflict [lhs is the justification; rhs is propagated 1]; 
            // 2 ... continue; --||-- [rhs is the justification; lhs is propagated 0]; 
            // 3 ... conflict; lhs is for sure greater than rhs; 
            // 4 ... invalid (should not happen)
            0, /*(z, z)*/ 0, /*(0, z)*/ 1, /*(1, z)*/ 4, /*(x, z)*/
            2, /*(z, 0)*/ 2, /*(0, 0)*/ 3, /*(1, 0)*/ 4, /*(x, 0)*/
            0, /*(z, 1)*/ 0, /*(0, 1)*/ 1, /*(1, 1)*/ 4, /*(x, 1)*/
            // for the positive case (vice-versa for negative case -> we swap lhs/rhs + special treatment for index 0)
        };
        unsigned i = sz;
        for (; i > (unsigned)!is_positive && !conflict; i--) {
            tbit l = lhs_val[i - 1];
            tbit r = rhs_val[i - 1];
            
            unsigned char action = action_lookup[l | (r << 2)];
            switch (action) {
                case 0:
                    i = 0;
                    break;
                case 1:
                case 3:
                    dep.push_back({ lhs, i - 1 });
                    LOG("Added dependency: pdd: " << lhs << " idx: " << i - 1);
                    conflict = !s.m_fixed_bits.fix_bit(s, rhs, i - 1, BIT_1, bit_justification_constraint::mk(s, this, dep), true);
                    SASSERT((action != 3) == conflict);
                    break;
                case 2:
                    dep.push_back({ rhs, i - 1 });
                    LOG("Added dependency: pdd: " << rhs << " idx: " << i - 1);
                    conflict = !s.m_fixed_bits.fix_bit(s, lhs, i - 1, BIT_0, bit_justification_constraint::mk(s, this, dep), true);
                    SASSERT(!conflict);
                    break;
                default:
                    VERIFY(false);
            }
        }
        if (!conflict && !is_positive && i == 1) {
            // Special treatment for lhs < rhs (note: we swapped lhs <-> rhs so this is really a less and not a greater)
            conflict = !s.m_fixed_bits.fix_bit(s, lhs, 0, BIT_0, bit_justification_constraint::mk(s, this, dep), true);
            if (!conflict)
                conflict = !s.m_fixed_bits.fix_bit(s, rhs, 0, BIT_1, bit_justification_constraint::mk(s, this, dep), true);
        }
        SASSERT(
                is_positive && conflict == (fixed_bits::min_max(lhs_val).first > fixed_bits::min_max(rhs_val).second) ||
                !is_positive && conflict == (fixed_bits::min_max(lhs_val).second <= fixed_bits::min_max(rhs_val).first)
        );
        return !conflict;
    }

    unsigned ule_constraint::hash() const {
    	return mk_mix(lhs().hash(), rhs().hash(), kind());
    }

    bool ule_constraint::operator==(constraint const& other) const {
        return other.is_ule() && lhs() == other.to_ule().lhs() && rhs() == other.to_ule().rhs();
    }

    void ule_constraint::add_to_univariate_solver(pvar v, solver& s, univariate_solver& us, unsigned dep, bool is_positive) const {
        pdd p = s.subst(lhs());
        pdd q = s.subst(rhs());
        bool p_ok = p.is_univariate_in(v);
        bool q_ok = q.is_univariate_in(v);
        IF_VERBOSE(10, display(verbose_stream() << ";; ", to_lbool(is_positive), p, q) << "\n");
        if (!is_positive && !q_ok)  // add p > 0
            us.add_ugt(p.get_univariate_coefficients(), rational::zero(), false, dep);
        if (!is_positive && !p_ok)  // add -1 > q  <==>  q+1 > 0
            us.add_ugt((q + 1).get_univariate_coefficients(), rational::zero(), false, dep);
        if (p_ok && q_ok)
            us.add_ule(p.get_univariate_coefficients(), q.get_univariate_coefficients(), !is_positive, dep);
    }
}
