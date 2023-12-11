/*++
Copyright (c) 2022 Microsoft Corporation

Module Name:

    Extract fixed bits from constraints

Author:

    Jakob Rath, Nikolaj Bjorner (nbjorner), Clemens Eisenhofer 2022-08-22

--*/

#include "sat/smt/polysat/fixed_bits.h"
#include "sat/smt/polysat/ule_constraint.h"

namespace polysat {

    /**
     * 2^k * x = 2^k * b
     * ==> x[N-k-1:0] = b[N-k-1:0]
     */
    bool get_eq_fixed_lsb(pdd const& p, fixed_bits& out) {
        SASSERT(!p.is_val());
        unsigned const N = p.power_of_2();
        // Recognize p = 2^k * a * x - 2^k * b
        if (!p.hi().is_val())
            return false;
        if (!p.lo().is_val())
            return false;
        // p = c * x - d
        rational const c = p.hi().val();
        rational const d = (-p.lo()).val();
        SASSERT(!c.is_zero());
#if 1
        // NOTE: ule_constraint::simplify removes odd factors of the leading term
        unsigned k;
        VERIFY(c.is_power_of_two(k));
        if (d.parity(N) < k)
            return false;
        rational const b = machine_div2k(d, k);
        out = fixed_bits(N - k - 1, 0, b);
        SASSERT_EQ(d, b * rational::power_of_two(k));
        SASSERT_EQ(p, (p.manager().mk_var(p.var()) - out.value) * rational::power_of_two(k));
        return true;
#else
        // branch if we want to support non-simplifed constraints (not recommended)
        //
        // 2^k * a * x = 2^k * b
        // ==> x[N-k-1:0] = a^-1 * b[N-k-1:0]
        // for odd a
        unsigned k = c.parity(N);
        if (d.parity(N) < k)
            return false;
        rational const a = machine_div2k(c, k);
        SASSERT(a.is_odd());
        SASSERT(a.is_one());  // TODO: ule-simplify will multiply with a_inv already, so we can drop the check here.
        rational a_inv;
        VERIFY(a.mult_inverse(N, a_inv));
        rational const b = machine_div2k(d, k);
        out.hi = N - k - 1;
        out.lo = 0;
        out.value = a_inv * b;
        SASSERT_EQ(p, (p.manager().mk_var(p.var()) - out.value) * a * rational::power_of_two(k));
        return true;
#endif
    }

    bool get_eq_fixed_bits(pdd const& p, fixed_bits& out) {
        if (get_eq_fixed_lsb(p, out))
            return true;
        return false;
    }

    /**
     * Constraint lhs <= rhs.
     *
     * -2^(k - 2) * x > 2^(k - 1)
     * <=> 2 + x[1:0] > 2  (mod 4)
     * ==> x[1:0] = 1
     *    -- TODO: Generalize [the obvious solution does not work]
     */
    bool get_ule_fixed_lsb(pdd const& lhs, pdd const& rhs, bool is_positive, fixed_bits& out) {
        return false;
    }

    /**
     * Constraint lhs <= rhs.
     *
     * x <= 2^k - 1  ==>  x[N-1:k] = 0
     * x <  2^k      ==>  x[N-1:k] = 0
     */
    bool get_ule_fixed_msb(pdd const& p, pdd const& q, bool is_positive, fixed_bits& out) {
        SASSERT(!q.is_zero());  // equalities are handled elsewhere
        unsigned const N = p.power_of_2();
        pdd const& lhs = is_positive ? p : q;
        pdd const& rhs = is_positive ? q : p;
        bool const is_strict = !is_positive;
        if (lhs.is_var() && rhs.is_val()) {
            // x <= c
            // find smallest k such that c <= 2^k - 1, i.e., c+1 <= 2^k
            // ==>  x <= 2^k - 1  ==> x[N-1:k] = 0
            //
            // x < c
            // find smallest k such that c <= 2^k
            // ==>  x < 2^k  ==> x[N-1:k] = 0
            rational const c = is_strict ? rhs.val() : (rhs.val() + 1);
            unsigned const k = c.next_power_of_two();
            if (k < N) {
                out.hi = N - 1;
                out.lo = k;
                out.value = 0;
                return true;
            }
        }
        return false;
    }

    // 2^(N-1) <= 2^(N-1-i) * x
    bool get_ule_fixed_bit(pdd const& p, pdd const& q, bool is_positive, fixed_bits& out) {
        return false;
    }

    bool get_ule_fixed_bits(pdd const& lhs, pdd const& rhs, bool is_positive, fixed_bits& out) {
        SASSERT(ule_constraint::is_simplified(lhs, rhs));
        if (rhs.is_zero())
            return is_positive ? get_eq_fixed_bits(lhs, out) : false;
        if (get_ule_fixed_msb(lhs, rhs, is_positive, out))
            return true;
        if (get_ule_fixed_lsb(lhs, rhs, is_positive, out))
            return true;
        if (get_ule_fixed_bit(lhs, rhs, is_positive, out))
            return true;
        return false;
    }

    bool get_fixed_bits(signed_constraint c, fixed_bits& out) {
        SASSERT_EQ(c.vars().size(), 1);  // this only makes sense for univariate constraints
        if (c.is_ule())
            return get_ule_fixed_bits(c.to_ule().lhs(), c.to_ule().rhs(), c.is_positive(), out);
        // if (c->is_op())
        //     ;  // TODO:  x & constant = constant   ==> bitmask ... but we have trouble recognizing that because we introduce a new variable for '&' before we see the equality.
        return false;
    }




/*
    // 2^(k - d) * x = m * 2^(k - d)
    // Special case [still seems to occur frequently]: -2^(k - 2) * x > 2^(k - 1) - TODO: Generalize [the obvious solution does not work] => lsb(x, 2) = 1
    bool get_lsb(pdd lhs, pdd rhs, pdd& p, trailing_bits& info, bool pos) {
        SASSERT(lhs.is_univariate() && lhs.degree() <= 1);
        SASSERT(rhs.is_univariate() && rhs.degree() <= 1);

        else { // inequality - check for special case
            if (pos || lhs.power_of_2() < 3)
                return false;
            auto it = lhs.begin();
            if (it == lhs.end())
                return false;
            if (it->vars.size() != 1)
                return false;
            rational coeff = it->coeff;
            it++;
            if (it != lhs.end())
                return false;
            if ((mod2k(-coeff, lhs.power_of_2())) != rational::power_of_two(lhs.power_of_2() - 2))
                return false;
            p = lhs.div(coeff);
            SASSERT(p.is_var());
            info.bits = 1;
            info.length = 2;
            info.positive = true; // this is a conjunction
            return true;
        }
    }
*/

}  // namespace polysat
