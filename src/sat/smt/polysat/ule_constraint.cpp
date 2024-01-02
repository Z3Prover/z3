/*++
Copyright (c) 2021 Microsoft Corporation

Module Name:

    polysat unsigned <= constraints

Author:

    Nikolaj Bjorner (nbjorner) 2021-03-19
    Jakob Rath 2021-04-06

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

    p <= q  &&  q+1 != 0    ==>  p+1 <= q+1

    p <= q  &&  p != 0      ==>   -q <= -p

--*/

#include "util/log.h"
#include "sat/smt/polysat/core.h"
#include "sat/smt/polysat/constraints.h"
#include "sat/smt/polysat/ule_constraint.h"

namespace polysat {

    // Simplify lhs <= rhs.
    //
    // NOTE: the result should not depend on the initial value of is_positive;
    //       the purpose of is_positive is to allow flipping the sign as part of a rewrite rule.
    static void simplify_impl(bool& is_positive, pdd& lhs, pdd& rhs) {
        
        SASSERT_EQ(lhs.power_of_2(), rhs.power_of_2());
        unsigned const N = lhs.power_of_2();

        // verbose_stream() << "simplify " << lhs << " <= " << rhs << "\n";

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
        if (!lhs.is_val() && !rhs.is_val()) {
            unsigned const lhs_vars = lhs.free_vars().size();
            unsigned const rhs_vars = rhs.free_vars().size();
            unsigned const diff_vars = (lhs - rhs).free_vars().size();
            if (diff_vars < lhs_vars || diff_vars < rhs_vars) {
                LOG("reduce number of varables");
                // verbose_stream() << "IN:  " << ule_pp(to_lbool(is_positive), lhs, rhs) << "\n";
                if (lhs_vars <= rhs_vars)
                    rhs = lhs - rhs - 1;
                else
                    lhs = rhs - lhs;
                // verbose_stream() << "OUT: " << ule_pp(to_lbool(is_positive), lhs, rhs) << "\n";
            }
        }

        if (rhs.is_val() && !rhs.is_zero() && lhs.offset() == rhs.val()) {
            TRACE("bv", tout << "- p + k <= k-->  p <= k\n");
            lhs = rhs - lhs;
        }

        if (lhs.is_val() && !lhs.is_zero() && lhs.val() == rhs.offset()) {
            TRACE("bv", tout << "k <= p + k       -->  p <= -k-1\n");
            pdd k = lhs;
            lhs = rhs - lhs;
            rhs = -k - 1;
        }

        if (lhs.is_val() && rhs.leading_coefficient().get_bit(N - 1) && !rhs.offset().is_zero()) {
            TRACE("bv", tout << "k <= -p-->  p - 1 <= -k - 1\n");
            pdd k = lhs;
            lhs = -(rhs + 1);
            rhs = -k - 1;
        }

        if (rhs.is_val() && lhs.leading_coefficient().get_bit(N - 1) && !lhs.offset().is_zero()) {
            TRACE("bv", tout << "-p <= k          -->  -k-1 <= p-1\n");
            pdd k = rhs;
            rhs = -(lhs + 1);
            lhs = -k - 1;
        }

        if (rhs.is_zero() && lhs.leading_coefficient().get_bit(N - 1) && !lhs.offset().is_zero()) {
            TRACE("bv", tout << "-p <= 0          -->  p <= 0\n");
            lhs = -lhs;
        }
        // NOTE: do not use pdd operations in conditions when comparing pdd values.
        //       e.g.: "lhs.offset() == (rhs + 1).val()" is problematic with the following evaluation:
        //          1. return reference into pdd_manager::m_values from lhs.offset()
        //          2. compute rhs+1, which may reallocate pdd_manager::m_values
        //          3. now the reference returned from lhs.offset() may be invalid
        pdd const rhs_plus_one = rhs + 1;

        // TODO: potential bug here: first call offset(), then rhs+1 has to reallocate pdd_manager::m_values, then the reference to offset is broken.
        if (rhs.is_val() && !rhs.is_zero() && lhs.offset() == rhs_plus_one.val()) {
            TRACE("bv", tout << "p - k <= -k - 1  -->  k <= p\n");
            pdd k = -(rhs + 1);
            rhs = lhs + k;
            lhs = k;
        }

        pdd const lhs_minus_one = lhs - 1;

        // k <= 2^(N-1)*p + q + k-1  -->  k <= 2^(N-1)*p - q
        if (lhs.is_val() && rhs.leading_coefficient() == rational::power_of_two(N-1) && rhs.offset() == lhs_minus_one.val()) {
            TRACE("bv", tout << "k <= 2^(N-1)*p + q + k-1  -->  k <= 2^(N-1)*p - q\n");
            rhs = (lhs - 1) - rhs;
        }

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
        // verbose_stream() << "simplified " << lhs << " <= " << rhs << "\n";
    } // simplify_impl
}


namespace polysat {

    ule_constraint::ule_constraint(pdd const& l, pdd const& r, pdd const& ul, pdd const& ur) :
        m_lhs(l), m_rhs(r), m_unfold_lhs(ul), m_unfold_rhs(ur) {

        SASSERT_EQ(m_lhs.power_of_2(), m_rhs.power_of_2());

        vars().append(m_lhs.free_vars());
        for (auto v : m_rhs.free_vars())
            if (!vars().contains(v))
                vars().push_back(v);

        m_unfold_vars.append(m_unfold_lhs.free_vars());
        for (auto v : m_unfold_rhs.free_vars())
            if (!m_unfold_vars.contains(v))
                m_unfold_vars.push_back(v);
    }

    void ule_constraint::simplify(bool& is_positive, pdd& lhs, pdd& rhs) {
        SASSERT_EQ(lhs.power_of_2(), rhs.power_of_2());
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
        SASSERT(is_simplified(lhs, rhs));  // rewriting should be idempotent
#endif
    }

    bool ule_constraint::is_simplified(pdd const& lhs0, pdd const& rhs0) {
        bool const pos0 = true;
        bool pos1 = pos0;
        pdd lhs1 = lhs0;
        pdd rhs1 = rhs0;
        simplify_impl(pos1, lhs1, rhs1);
        bool const is_simplified = (pos1 == pos0 && lhs1 == lhs0 && rhs1 == rhs0);
        DEBUG_CODE({
            // check that simplification doesn't depend on initial sign
            bool pos2 = !pos0;
            pdd lhs2 = lhs0;
            pdd rhs2 = rhs0;
            simplify_impl(pos2, lhs2, rhs2);
            SASSERT_EQ(pos2, !pos1);
            SASSERT_EQ(lhs2, lhs1);
            SASSERT_EQ(rhs2, rhs1);
        });
        return is_simplified;
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
        display(out, l_true, m_lhs, m_rhs);
        if (m_lhs != m_unfold_lhs || m_rhs != m_unfold_rhs)
            display(out << " alias (", l_true, m_unfold_lhs, m_unfold_rhs) << ")";
        return out;
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

    lbool ule_constraint::eval_unfold(assignment const& a) const {
        return eval(a.apply_to(unfold_lhs()), a.apply_to(unfold_rhs()));
    }

    void ule_constraint::activate(core& c, bool sign, dependency const& d) {
        auto p = c.subst(lhs());
        auto q = c.subst(rhs());
        auto& C = c.cs();
        if (sign && !lhs().is_val() && !rhs().is_val()) {
            c.add_axiom("lhs > rhs  ==>  -1 > rhs", { d, C.ult(rhs(), -1) }, false);
            c.add_axiom("lhs > rhs  ==>  lhs > 0", { d, C.ult(0, lhs()) }, false);
        }
    }


}
