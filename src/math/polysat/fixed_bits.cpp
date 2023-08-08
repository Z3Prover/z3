/*++
Copyright (c) 2022 Microsoft Corporation

Module Name:

    Extract fixed bits from constraints

Author:

    Jakob Rath, Nikolaj Bjorner (nbjorner), Clemens Eisenhofer 2022-08-22

--*/

#include "math/polysat/fixed_bits.h"
#include "math/polysat/ule_constraint.h"
#include "math/polysat/clause.h"

namespace polysat {

    /**
     * Constraint lhs <= rhs.
     *
     * 2^(k - d) * x = 2^(k - d) * c
     * ==> x[|d|:0] = c[|d|:0]
     *
     * -2^(k - 2) * x > 2^(k - 1)
     * <=> 2 + x[1:0] > 2  (mod 4)
     * ==> x[1:0] = 1
     *    -- TODO: Generalize [the obvious solution does not work]
     */

    /**
     * 2^(k - d) * x = 2^(k - d) * c
     * ==> x[|d|:0] = c[|d|:0]
     */
    bool get_eq_fixed_lsb(pdd const& p, fixed_bits& out) {
        if (!p.hi().is_val())
            return false;
        // TODO:
        return false;
    }

    bool get_eq_fixed_bits(pdd const& p, fixed_bits& out) {
        return get_eq_fixed_lsb(p, out);
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

    bool get_ule_fixed_bits(pdd const& lhs, pdd const& rhs, bool is_positive, fixed_bits& out) {
        return false;
    }

    bool get_fixed_bits(signed_constraint c, fixed_bits& out) {
        SASSERT_EQ(c->vars().size(), 1);  // this only makes sense for univariate constraints
        if (c->is_ule())
            return get_ule_fixed_bits(c->to_ule().lhs(), c->to_ule().rhs(), c.is_positive(), out);
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

        if (rhs.is_zero()) { // equality
            auto lhs_decomp = decouple_constant(lhs);

            lhs = lhs_decomp.first;
            rhs = -lhs_decomp.second;

            SASSERT(rhs.is_val());

            unsigned k = lhs.manager().power_of_2();
            unsigned d = lhs.max_pow2_divisor();
            unsigned span = k - d;
            if (span == 0 || lhs.is_val())
                return false;

            p = lhs.div(rational::power_of_two(d));
            rational rhs_val = rhs.val();
            info.bits = rhs_val / rational::power_of_two(d);
            if (!info.bits.is_int())
                return false;

            SASSERT(lhs.is_univariate() && lhs.degree() <= 1);

            auto it = p.begin();
            auto first = *it;
            it++;
            if (it == p.end()) {
                // if the lhs contains only one monomial it is of the form: odd * x = mask. We can multiply by the inverse to get the mask for x
                SASSERT(first.coeff.is_odd());
                rational inv;
                VERIFY(first.coeff.mult_inverse(lhs.power_of_2(), inv));
                p *= inv;
                info.bits = mod2k(info.bits * inv, span);
            }

            info.length = span;
            info.positive = pos;
            return true;
        }
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
