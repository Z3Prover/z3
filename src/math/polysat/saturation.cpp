/*++
Copyright (c) 2021 Microsoft Corporation

Module Name:

    Polysat core saturation

Author:

    Nikolaj Bjorner (nbjorner) 2021-03-19
    Jakob Rath 2021-04-6

TODO:
- saturation instantiates lemmas that are used for unit propagation.
- the unit propagated constraint should/could be added to Gamma & core and enable simpler conflict resolution.

TODO: preserve falsification
- each rule selects a certain premise that is problematic, 
  We assume that problematic premises are false in the current assignment
  The derived consequence should also be false in the current assignment to be effective, but simpler so that we can resolve.

TODO:
- remove level information from created constraints.
- 
--*/
#include "math/polysat/saturation.h"
#include "math/polysat/solver.h"
#include "math/polysat/log.h"

namespace polysat {

    constraint_manager& inference_engine::cm() { return s().m_constraints; }
    
    bool inf_saturate::perform(pvar v, conflict_core& core) {
        for (auto c1 : core) {
            auto c = c1.as_inequality();
            if (try_ugt_x(v, core, c))
                return true;
            if (try_ugt_y(v, core, c))
                return true;
            if (try_ugt_z(v, core, c))
                return true;
            if (try_y_l_ax_and_x_l_z(v, core, c))
                return true;
        }
        return false;
    }

    signed_constraint inf_saturate::ineq(unsigned lvl, bool is_strict, pdd const& lhs, pdd const& rhs) {
        if (is_strict)
            return s().m_constraints.ult(lvl, lhs, rhs);
        else
            return s().m_constraints.ule(lvl, lhs, rhs);
    }

    void inf_saturate::push_c(conflict_core& core, signed_constraint const& c, clause_builder& reason) {
        core.insert(c);
        clause_ref lemma = reason.build();
        s().add_lemma(lemma);
        s().propagate_bool(c.blit(), lemma.get());
    }

    void inf_saturate::push_l(conflict_core& core, unsigned lvl, bool is_strict, pdd const& lhs, pdd const& rhs, clause_builder& reason) {
        signed_constraint c = ineq(lvl, is_strict, lhs, rhs);
        push_c(core, c, reason);
    }

    /// Find smallest upper bound for the variable x, i.e., a constraint 'x <= bound' where the rhs is constant.
    bool inf_saturate::find_upper_bound(pvar x, signed_constraint& c, rational& bound) {
        auto& bounds = s().m_cjust[x];
        rational best_bound(-1);
        pdd y = s().var(x);
        for (auto& b : bounds) {
            inequality bound = b.as_inequality();
            if (is_x_l_Y(x, bound, y) && y.is_val()) {
                rational value = y.val();
                if (bound.is_strict) {
                    SASSERT(value > 0);  // "x < 0" is always false and should have led to a conflict earlier
                    value = value - 1;
                }
                if (value < best_bound) {
                    best_bound = value;
                    c = b;
                }
            }
        }
        return best_bound != -1;
    }


    /// Add Ω*(x, y) to the conflict state.
    ///
    /// @param[in] p    bit width
    bool inf_saturate::push_omega_mul(conflict_core& core, clause_builder & reason, unsigned level, pdd const& x, pdd const& y) {
        LOG_H3("Omega^*(x, y)");
        LOG("x = " << x);
        LOG("y = " << y);
        auto& pddm = x.manager();   
        unsigned p = pddm.power_of_2();
        unsigned min_k = 0;
        unsigned max_k = p - 1;
        unsigned k = p / 2;

        rational x_val;
        if (!s().try_eval(x, x_val))
            return false;

        rational y_val;
        if (!s().try_eval(y, y_val))
            return false;

        unsigned x_bits = x_val.bitsize();
        LOG("eval x: " << x << " := " << x_val << " (x_bits: " << x_bits << ")");
        SASSERT(x_val < rational::power_of_two(x_bits));
        min_k = x_bits;

        unsigned y_bits = y_val.bitsize();
        LOG("eval y: " << y << " := " << y_val << " (y_bits: " << y_bits << ")");
        SASSERT(y_val < rational::power_of_two(y_bits));
        max_k = p - y_bits;

        if (min_k > max_k) {
            // In this case, we cannot choose k such that both literals are false.
            // This means x*y overflows in the current model and the chosen rule is not applicable.
            // (or maybe we are in the case where we need the msb-encoding for overflow).
            return false;
        }

        SASSERT(min_k <= max_k);  // if this assertion fails, we cannot choose k s.t. both literals are false

        // TODO: could also choose other value for k (but between the bounds)
        if (min_k == 0)
            k = max_k;
        else
            k = min_k;

        SASSERT(min_k <= k && k <= max_k);

        // x < 2^k
        auto c1 = s().m_constraints.ult(level, x, pddm.mk_val(rational::power_of_two(k)));
        // y <= 2^{p-k}
        auto c2 = s().m_constraints.ule(level, y, pddm.mk_val(rational::power_of_two(p - k)));

        // bail-out explanation uses equality constraint based on current assignment to variables.
        // TODO: extract stronger explanations.
        // for example if they appear already in Gamma
        // or if some strengthening appears in gamma
        // or using the current value assignment

        clause_builder bound(s());
        bound.push(s().m_constraints.eq(level, x - pddm.mk_val(x_val)));
        push_c(core, c1, bound);
        bound.reset();

        bound.push(s().m_constraints.eq(level, y - pddm.mk_val(y_val)));
        push_c(core, c2, bound);


        reason.push(c1);
        reason.push(c2);
        return true;
    }

    // special case viable sets used by variables.
    bool inf_saturate::push_omega_viable(conflict_core& core, clause_builder& reason, unsigned level, pdd const& px, pdd const& py) {
        if (!px.is_var() || !py.is_var())
            return false;
        pvar x = px.var();
        pvar y = py.var();
        rational x_max = s().m_viable.max_viable(x);
        rational y_max = s().m_viable.max_viable(y);
        auto& pddm = px.manager();
        unsigned bit_size = pddm.power_of_2();
        rational bound = rational::power_of_two(bit_size);
        if (x_max * y_max < bound) {
            // max values don't overflow, we can justify no-overflow using cjust for x, y
            for (auto c : s().m_cjust[x])
                reason.push(c);
            for (auto c : s().m_cjust[y])
                reason.push(c);
            return true;
        }
        
        rational x_val = s().get_value(x);
        rational y_val = s().get_value(y);

        if (x_val * y_val >= bound)
            return false;

        rational x_lo = x_val, x_hi = x_max, y_lo = y_val, y_hi = y_max;
        rational two(2);
        while (x_lo < x_hi || y_lo < y_hi) {
            rational x_mid = div(x_hi + x_lo, two);
            rational y_mid = div(y_hi + y_lo, two);
            if (x_mid * y_mid >= bound)
                x_hi = x_mid - 1, y_hi = y_mid - 1;
            else
                x_lo = x_mid, y_lo = y_mid;            
        }
        SASSERT(x_hi == x_lo && y_hi == y_lo);
        SASSERT(x_lo * y_lo < bound);
        SASSERT((x_lo + 1) * (y_lo + 1) >= bound);
        if ((x_lo + 1) * y_lo < bound) {
            x_hi = x_max;
            while (x_lo < x_hi) {
                rational x_mid = div(x_hi + x_lo, two);
                if (x_mid * y_lo >= bound)
                    x_hi = x_mid - 1;
                else
                    x_lo = x_mid;
            }
        }
        else if (x_lo * (y_lo + 1) < bound) {
            y_hi = y_max;
            while (y_lo < y_hi) {
                rational y_mid = div(y_hi + y_lo, two);
                if (y_mid * x_lo >= bound)
                    y_hi = y_mid - 1;
                else
                    y_lo = y_mid;
            }
        }
        SASSERT(x_lo * y_lo < bound);
        SASSERT((x_lo + 1) * y_lo >= bound);
        SASSERT(x_lo * (y_lo + 1) >= bound);

        // inequalities are justified by current assignments to px, py
        // conflict resolution should be able to pick up this as a valid justification.
        // or we resort to the same extension as in the original mul_overflow code
        // where we add explicit equality propagations from the current assignment.
        auto c1 = s().m_constraints.ule(level, px, pddm.mk_val(x_lo));
        auto c2 = s().m_constraints.ule(level, py, pddm.mk_val(y_lo));
        reason.push(c1);
        reason.push(c2);
        return true;
    }

    /*
    * Match [v] .. <= v 
    */
    bool inf_saturate::is_l_v(pvar v, inequality const& i) {
        return i.rhs == s().var(v);
    }

    /*
    * Match [v] v <= ...
    */
    bool inf_saturate::is_g_v(pvar v, inequality const& i) {
        return i.lhs == s().var(v);
    }

    /*
    * Match [x] x <= y
    */
    bool inf_saturate::is_x_l_Y(pvar x, inequality const& c, pdd& y) {
        y = c.rhs;
        return is_g_v(x, c);
    }

    /*
    * Match [x] y <= a*x
    */
    bool inf_saturate::is_Y_l_Ax(pvar x, inequality const& d, pdd& a, pdd& y) {
        y = d.lhs;
        return is_xY(x, d.rhs, a);
    }

    bool inf_saturate::verify_Y_l_Ax(pvar x, inequality const& d, pdd const& a, pdd const& y) {        
        return d.lhs == y && d.rhs == a * s().var(x);
    }

    /**
    * Match [v] v*x <= z*x
    */
    bool inf_saturate::is_Xy_l_XZ(pvar v, inequality const& c, pdd& x, pdd& z) {
        if (!is_xY(v, c.lhs, x))
            return false;

        // TODO: in principle, 'x' could be any polynomial. However, we need to divide the lhs by x, and we don't have general polynomial division yet.
        //       so for now we just allow the form 'value*variable'.
        //        (extension to arbitrary monomials for 'x' should be fairly easy too)
        if (!x.is_unary())
            return false;
        rational x_coeff = x.hi().val();
        pdd xz = x;
        return c.rhs.try_div(x_coeff, xz) && xz.factor(x.var(), 1, z);
    }

    bool inf_saturate::verify_Xy_l_XZ(pvar v, inequality const& c, pdd const& x, pdd const& z) {
        return c.lhs == s().var(v) * x && c.rhs == z * x;
    }

    /**
    * Match [z] yx <= zx
    */
    bool inf_saturate::is_YX_l_zX(pvar z, inequality const& c, pdd& x, pdd& y) {
        if (!is_xY(z, c.rhs, x))
            return false;
        // TODO: in principle, 'x' could be any polynomial. However, we need to divide the lhs by x, and we don't have general polynomial division yet.
        //       so for now we just allow the form 'value*variable'.
        //       (extension to arbitrary monomials for 'x' should be fairly easy too)
        if (!x.is_unary())
            return false;

        unsigned x_var = x.var();
        rational x_coeff = x.hi().val();
        pdd xy = x;
        return c.lhs.try_div(x_coeff, xy) && xy.factor(x_var, 1, y);
    }

    bool inf_saturate::verify_YX_l_zX(pvar z, inequality const& c, pdd const& x, pdd const& y) {
        return c.lhs == y * x && c.rhs == s().var(z) * x;
    }

    /**
    * Match [x] xY <= xZ
    */
    bool inf_saturate::is_xY_l_xZ(pvar x, inequality const& c, pdd& y, pdd& z) {
        return is_xY(x, c.lhs, y) && is_xY(x, c.rhs, z);
    }

    /**
    * Match xy = x * Y
    */
    bool inf_saturate::is_xY(pvar x, pdd const& xy, pdd& y) {
        return xy.degree(x) == 1 && xy.factor(x, 1, y);
    }

    /**
     * Implement the inferences
     *  [x] zx > yx  ==>  Ω*(x,y) \/ z > y
     *  [x] yx <= zx  ==>  Ω*(x,y) \/ y <= z
     */
    bool inf_saturate::try_ugt_x(pvar v, conflict_core& core, inequality const& c) {
        pdd x = s().var(v);
        pdd y = x;
        pdd z = x;
        if (!is_xY_l_xZ(v, c, y, z))
            return false;

        unsigned const lvl = c.src->level();

        clause_builder reason(s());
        // Omega^*(x, y)
        if (!push_omega_mul(core, reason, lvl, x, y))
            return false;
        push_l(core, lvl, c.is_strict, y, z, reason);

        return true;
    }

    /// [y] z' <= y /\ zx > yx  ==>  Ω*(x,y) \/ zx > z'x
    /// [y] z' <= y /\ yx <= zx  ==>  Ω*(x,y) \/ z'x <= zx
    bool inf_saturate::try_ugt_y(pvar v, conflict_core& core, inequality const& le_y, inequality const& yx_l_zx, pdd const& x, pdd const& z) {
        LOG_H3("Try z' <= y && zx > yx where y := v" << v);
        pdd const y = s().var(v);

        SASSERT(is_l_v(v, le_y));
        SASSERT(verify_Xy_l_XZ(v, yx_l_zx, x, z));
          
        unsigned const lvl = std::max(yx_l_zx.src->level(), le_y.src->level());
        pdd const& z_prime = le_y.lhs;

        clause_builder reason(s());
        // Omega^*(x, y)
        if (!push_omega_mul(core, reason, lvl, x, y))
            return false;

        // z'x <= zx
        push_l(core, lvl, yx_l_zx.is_strict || le_y.is_strict, z_prime * x, z * x, reason);

        return true;
    }

    bool inf_saturate::try_ugt_y(pvar v, conflict_core& core, inequality const& c) {
        if (!is_l_v(v, c))
            return false;
        pdd x = s().var(v);
        pdd z = x;
        for (auto dd : core) {
            auto d = dd.as_inequality();
            if (is_Xy_l_XZ(v, d, x, z) && try_ugt_y(v, core, c, d, x, z))
                return true;
        }
        return false;
    }


    /// [x]  y <= ax /\ x <= z  (non-overflow case)
    ///     ==>   Ω*(a, z)  \/  y <= az
    bool inf_saturate::try_y_l_ax_and_x_l_z(pvar x, conflict_core& core, inequality const& c) {
        if (!is_g_v(x, c))
            return false;

        pdd y = s().var(x);
        pdd a = y;
        for (auto dd : core) {
            auto d = dd.as_inequality();
            if (is_Y_l_Ax(x, d, a, y) && try_y_l_ax_and_x_l_z(x, core, c, d, a, y))
                return true;
        }
        return false;
    }

    bool inf_saturate::try_y_l_ax_and_x_l_z(pvar x, conflict_core& core, inequality const& x_l_z, inequality const& y_l_ax, pdd const& a, pdd const& y) {

        SASSERT(is_g_v(x, x_l_z));
        SASSERT(verify_Y_l_Ax(x, y_l_ax, a, y));
        pdd z = x_l_z.rhs;
        unsigned const lvl = std::max(x_l_z.src->level(), y_l_ax.src->level());
        clause_builder reason(s());
        if (!push_omega_mul(core, reason, lvl, a, z))
            return false;
        push_l(core, lvl, x_l_z.is_strict || y_l_ax.is_strict, y, a * z, reason);
        return true;
    }


    /// [z] z <= y' /\ zx > yx  ==>  Ω*(x,y') \/ y'x > yx
    /// [z] z <= y' /\ yx <= zx  ==>  Ω*(x,y') \/ yx <= y'x
    bool inf_saturate::try_ugt_z(pvar z, conflict_core& core, inequality const& c) {
        if (!is_g_v(z, c))
            return false;

        pdd y = s().var(z);
        pdd x = y;
        for (auto dd : core) {
            auto d = dd.as_inequality();
            if (is_YX_l_zX(z, d, x, y) && try_ugt_z(z, core, c, d, x, y))
                return true;
        }
        return false;
    }

    bool inf_saturate::try_ugt_z(pvar z, conflict_core& core, inequality const& c, inequality const& d, pdd const& x, pdd const& y) {
        SASSERT(is_g_v(z, c));
        SASSERT(verify_YX_l_zX(z, d, x, y));
        unsigned const lvl = std::max(c.src->level(), d.src->level());
        pdd const& y_prime = c.rhs;
        clause_builder reason(s());
        // Omega^*(x, y')
        if (!push_omega_mul(core, reason, lvl, x, y_prime))
            return false;
        // yx <= y'x
        push_l(core, lvl, c.is_strict || d.is_strict, y * x, y_prime * x, reason);
        return true;
    }


}
