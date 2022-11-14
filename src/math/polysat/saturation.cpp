/*++
Copyright (c) 2021 Microsoft Corporation

Module Name:

    Polysat core saturation

Author:

    Nikolaj Bjorner (nbjorner) 2021-03-19
    Jakob Rath 2021-04-6


TODO: preserve falsification
- each rule selects a certain premises that are problematic.
  If the problematic premise is false under the current assignment, the newly inferred
  literal should also be false in the assignment in order to preserve conflicts.


TODO: when we check that 'x' is "unary":
- in principle, 'x' could be any polynomial. However, we need to divide the lhs by x, and we don't have general polynomial division yet.
  so for now we just allow the form 'value*variable'.
   (extension to arbitrary monomials for 'x' should be fairly easy too)

--*/
#include "math/polysat/saturation.h"
#include "math/polysat/solver.h"
#include "math/polysat/log.h"

namespace polysat {
    
    bool inf_saturate::perform(pvar v, conflict& core) {
        for (auto c1 : core) {
            if (!c1->is_ule())
                continue;
            if (c1.is_currently_true(s))
                continue;
            auto c = c1.as_inequality();
            if (try_ugt_x(v, core, c))
                return true;
            if (try_ugt_y(v, core, c))
                return true;
            if (try_ugt_z(v, core, c))
                return true;
            if (try_y_l_ax_and_x_l_z(v, core, c))
                return true;
            if (try_tangent(v, core, c))
                return true;
        }
        return false;
    }

    signed_constraint inf_saturate::ineq(bool is_strict, pdd const& lhs, pdd const& rhs) {
        if (is_strict)
            return s.ult(lhs, rhs);
        else
            return s.ule(lhs, rhs);
    }

    /**
    * Propagate c. It is added to reason and core all other literals in reason are false in current stack.
    * The lemmas outlined in the rules are valid and therefore c is implied.
    */
    bool inf_saturate::propagate(char const* inf_name, conflict& core, inequality const& _crit1, inequality const& _crit2, signed_constraint& c) {

        auto crit1 = _crit1.as_signed_constraint();
        auto crit2 = _crit2.as_signed_constraint();
        m_new_constraints.push_back(crit1);
        m_new_constraints.push_back(crit2);
        SASSERT(!crit1.is_currently_true(s));

        LOG("critical " << m_rule << " " << crit1);
        LOG("consequent " << c << " value: " << c.bvalue(s) << " is-false: " << c.is_currently_false(s) << " " << core.contains(~c));

        // ensure new core is a conflict
        // TODO: don't we need to check the m_new_constraints too? or maybe that is implicit in the rules (should check it)
        if (!c.is_currently_false(s) && c.bvalue(s) != l_false)
            return false;

        if (c.bvalue(s) == l_true)
            return false;

        // avoid loops
        // NOTE:
        // it is not enough to only check whether ~c is already in the core.
        // One example had c: 0 != 0, so c was ignored when inserting it to the core.
        // (But the side conditions in m_new_constraints were useful.)
        bool inserting = false;
        if (!c.is_always_false() && !core.contains(~c))
            inserting = true;
        else
            for (auto d : m_new_constraints)
                if (!d.is_always_true() && !core.contains(d)) {
                    inserting = true;
                    break;
                }
        if (!inserting)
            return false;

        // TODO: add as a side lemma instead of changing the conflict
        core.remove_all();
        for (auto d : m_new_constraints)
            core.insert_eval(d);
        if (c.bvalue(s) != l_false)  // conflict is due to the evaluation of c, so it depends on the variable values
            core.insert_vars(c);
        core.insert_eval(~c);
        core.logger().log(inf_name);
        LOG("Core " << core);
        return true;        
    }

    bool inf_saturate::propagate(char const* inf_name, conflict& core, inequality const& crit1, inequality const& crit2, bool is_strict, pdd const& lhs, pdd const& rhs) {
        signed_constraint c = ineq(is_strict, lhs, rhs);
        return propagate(inf_name, core, crit1, crit2, c);
    }

    /// Add premises for Ω*(x, y)
    void inf_saturate::push_omega_bisect(pdd const& x, rational x_max, pdd const& y, rational y_max) {
        rational x_val, y_val;
        auto& pddm = x.manager();
        rational bound = pddm.max_value();
        VERIFY(s.try_eval(x, x_val));
        VERIFY(s.try_eval(y, y_val));
        SASSERT(x_val * y_val <= bound);

        rational x_lo = x_val, x_hi = x_max, y_lo = y_val, y_hi = y_max;
        SASSERT(x_lo <= x_hi && y_lo <= y_hi);
        rational two(2);
        while (x_lo < x_hi || y_lo < y_hi) {
            rational x_mid = div(x_hi + x_lo + 1, two);
            rational y_mid = div(y_hi + y_lo + 1, two);
            if (x_mid * y_mid > bound) {
                x_hi = x_lo < x_hi ? x_mid - 1 : x_lo;
                y_hi = y_lo < y_hi ? y_mid - 1 : y_lo;
            }
            else
                x_lo = x_mid, y_lo = y_mid;
        }
        SASSERT(x_hi == x_lo && y_hi == y_lo);
        SASSERT(x_lo * y_lo <= bound);
        SASSERT((x_lo + 1) * (y_lo + 1) > bound);
        if ((x_lo + 1) * y_lo <= bound) {
            x_hi = x_max;
            while (x_lo < x_hi) {
                rational x_mid = div(x_hi + x_lo + 1, two);
                if (x_mid * y_lo > bound)
                    x_hi = x_mid - 1;
                else
                    x_lo = x_mid;
            }
        }
        else if (x_lo * (y_lo + 1) <= bound) {
            y_hi = y_max;
            while (y_lo < y_hi) {
                rational y_mid = div(y_hi + y_lo + 1, two);
                if (y_mid * x_lo > bound)
                    y_hi = y_mid - 1;
                else
                    y_lo = y_mid;
            }
        }
        SASSERT(x_lo * y_lo <= bound);
        SASSERT((x_lo + 1) * y_lo > bound || x_val == x_max);
        SASSERT(x_lo * (y_lo + 1) > bound || y_val == y_max);

        // inequalities are justified by current assignments to x, y
        // conflict resolution should be able to pick up this as a valid justification.
        // or we resort to the same extension as in the original mul_overflow code
        // where we add explicit equality propagations from the current assignment.
        auto c1 = s.ule(x, pddm.mk_val(x_lo));
        auto c2 = s.ule(y, pddm.mk_val(y_lo));
        m_new_constraints.insert(c1);
        m_new_constraints.insert(c2);
        LOG("bounded " << bound << " : " << x << " " << x_max << " " << y << " " << y_max << " " << c1 << " " << c2);
    }

    rational inf_saturate::max_value(pdd const& x) {
        if (x.is_var())
            return s.m_viable.max_viable(x.var());
        else if (x.is_val())
            return x.val();
        else
            return x.manager().max_value();
    }

    void inf_saturate::push_omega(pdd const& x, pdd const& y) {     
        m_new_constraints.insert(~s.umul_ovfl(x, y));
        /*
        // determine worst case upper bounds for x, y
        // then extract premises for a non-worst-case bound.
        auto& pddm = x.manager();
        rational x_max = max_value(x);
        rational y_max = max_value(y);
        
        LOG("pushing " << x << " " << y);

        if (x_max * y_max  > pddm.max_value())            
            push_omega_bisect(x, x_max, y, y_max);
        else {
            for (auto const& c : s.m_viable.get_constraints(y.var()))
                m_new_constraints.insert(c);
            for (auto const& c : s.m_viable.get_constraints(x.var()))
                m_new_constraints.insert(c);            
        }
        */
    }

    /*
    * Match [v] .. <= v 
    */
    bool inf_saturate::is_l_v(pvar v, inequality const& i) {
        return i.rhs == s.var(v);
    }

    /*
    * Match [v] v <= ...
    */
    bool inf_saturate::is_g_v(pvar v, inequality const& i) {
        return i.lhs == s.var(v);
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
        return d.lhs == y && d.rhs == a * s.var(x);
    }

    /**
    * Match [coeff*x] coeff*x*Y
    */

    bool inf_saturate::is_coeffxY(pdd const& x, pdd const& p, pdd& y) {
        pdd xy = x;
        return x.is_unary() && p.try_div(x.hi().val(), xy) && xy.factor(x.var(), 1, y);
    }

    /**
    * determine whether values of x * y is non-overflowing.
    */
    bool inf_saturate::is_non_overflow(pdd const& x, pdd const& y) {
        rational x_val, y_val;
        auto& pddm = x.manager();
        rational bound = rational::power_of_two(pddm.power_of_2());
        return s.try_eval(x, x_val) && s.try_eval(y, y_val) && x_val * y_val < bound;       
    }

    /**
    * Match [v] v*x <= z*x with x a variable
    */
    bool inf_saturate::is_Xy_l_XZ(pvar v, inequality const& c, pdd& x, pdd& z) {
        return is_xY(v, c.lhs, x) && is_coeffxY(x, c.rhs, z);
    }

    bool inf_saturate::verify_Xy_l_XZ(pvar v, inequality const& c, pdd const& x, pdd const& z) {
        return c.lhs == s.var(v) * x && c.rhs == z * x;
    }

    /**
    * Match [z] yx <= zx with x a variable
    */
    bool inf_saturate::is_YX_l_zX(pvar z, inequality const& c, pdd& x, pdd& y) {
        return is_xY(z, c.rhs, x) && is_coeffxY(x, c.lhs, y);
    }

    bool inf_saturate::verify_YX_l_zX(pvar z, inequality const& c, pdd const& x, pdd const& y) {
        return c.lhs == y * x && c.rhs == s.var(z) * x;
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
     *  [x] yx <= zx  ==>  Ω*(x,y) \/ y <= z \/ x = 0
     */
    bool inf_saturate::try_ugt_x(pvar v, conflict& core, inequality const& xy_l_xz) {
        set_rule("zx <= yx");
        pdd x = s.var(v);
        pdd y = x;
        pdd z = x;
        if (!is_xY_l_xZ(v, xy_l_xz, y, z))
            return false;
        if (!is_non_overflow(x, y))
            return false;
        if (!xy_l_xz.is_strict && s.get_value(v).is_zero())
            return false;

        m_new_constraints.reset();
        if (!xy_l_xz.is_strict)
            m_new_constraints.push_back(~s.eq(x));
        push_omega(x, y);
        return propagate("ugt_x", core, xy_l_xz, xy_l_xz, xy_l_xz.is_strict, y, z);
    }

    /// [y] z' <= y /\ zx > yx  ==>  Ω*(x,y) \/ zx > z'x
    /// [y] z' <= y /\ yx <= zx  ==>  Ω*(x,y) \/ z'x <= zx
    bool inf_saturate::try_ugt_y(pvar v, conflict& core, inequality const& le_y, inequality const& yx_l_zx, pdd const& x, pdd const& z) {
        SASSERT(is_l_v(v, le_y));
        SASSERT(verify_Xy_l_XZ(v, yx_l_zx, x, z));
        pdd const y = s.var(v);
        if (!is_non_overflow(x, y))
            return false;          
        pdd const& z_prime = le_y.lhs;
        m_new_constraints.reset();
        push_omega(x, y);
        return propagate("ugt_y", core, le_y, yx_l_zx, yx_l_zx.is_strict || le_y.is_strict, z_prime * x, z * x);
    }

    bool inf_saturate::try_ugt_y(pvar v, conflict& core, inequality const& yx_l_zx) {
        set_rule("[y] z' <= y & yx <= zx");
        pdd x = s.var(v);
        pdd z = x;
        if (!is_Xy_l_XZ(v, yx_l_zx, x, z))
            return false;
        for (auto si : s.m_search) {
            if (!si.is_boolean())
                continue;
            if (si.is_resolved())
                continue;
            auto dd = s.lit2cnstr(si.lit());
            if (!dd->is_ule())
                continue;
            auto le_y = dd.as_inequality();
            if (is_l_v(v, le_y) && try_ugt_y(v, core, le_y, yx_l_zx, x, z))
                return true;
        }
        return false;
    }


    /// [x]  y <= ax /\ x <= z  (non-overflow case)
    ///     ==>   Ω*(a, z)  \/  y <= az
    bool inf_saturate::try_y_l_ax_and_x_l_z(pvar x, conflict& core, inequality const& y_l_ax) {
        set_rule("[x] y <= ax & x <= z");
        pdd y = s.var(x);
        pdd a = y;
        if (!is_Y_l_Ax(x, y_l_ax, a, y))
            return false;
        if (a.is_one())
            return false;
        for (auto si : s.m_search) {
            if (!si.is_boolean())
                continue;
            if (si.is_resolved())
                continue;
            auto dd = s.lit2cnstr(si.lit());
            if (!dd->is_ule())
                continue;
            auto x_l_z = dd.as_inequality();
            if (is_g_v(x, x_l_z) && try_y_l_ax_and_x_l_z(x, core, y_l_ax, x_l_z, a, y))
                return true;
        }
        return false;
    }

    bool inf_saturate::try_y_l_ax_and_x_l_z(pvar x, conflict& core, inequality const& y_l_ax, inequality const& x_l_z,  pdd const& a, pdd const& y) {
        SASSERT(is_g_v(x, x_l_z));
        SASSERT(verify_Y_l_Ax(x, y_l_ax, a, y));
        pdd z = x_l_z.rhs;
        if (!is_non_overflow(a, z))
            return false;
        m_new_constraints.reset();       
        push_omega(a, z);
        return propagate("y_l_ax_and_x_l_z", core, y_l_ax, x_l_z, x_l_z.is_strict || y_l_ax.is_strict, y, a * z);
    }


    /// [z] z <= y' /\ zx > yx  ==>  Ω*(x,y') \/ y'x > yx
    /// [z] z <= y' /\ yx <= zx  ==>  Ω*(x,y') \/ yx <= y'x
    bool inf_saturate::try_ugt_z(pvar z, conflict& core, inequality const& yx_l_zx) {
        set_rule("[z] z <= y' && zx > yx");
        pdd y = s.var(z);
        pdd x = y;
        if (!is_YX_l_zX(z, yx_l_zx, x, y))
            return false;
        for (auto si : s.m_search) {
            if (!si.is_boolean())
                continue;
            if (si.is_resolved())
                continue;
            auto dd = s.lit2cnstr(si.lit());
            if (!dd->is_ule())
                continue;
            auto z_l_y = dd.as_inequality();
            if (is_g_v(z, z_l_y) && try_ugt_z(z, core, z_l_y, yx_l_zx, x, y))
                return true;
        }
        return false;
    }

    bool inf_saturate::try_ugt_z(pvar z, conflict& core, inequality const& z_l_y, inequality const& yx_l_zx, pdd const& x, pdd const& y) {
        SASSERT(is_g_v(z, z_l_y));
        SASSERT(verify_YX_l_zX(z, yx_l_zx, x, y));
        pdd const& y_prime = z_l_y.rhs;
        if (!is_non_overflow(x, y_prime))
            return false;
        m_new_constraints.reset();
        push_omega(x, y_prime);
        // yx <= y'x
        return propagate("ugt_z", core, yx_l_zx, z_l_y, z_l_y.is_strict || yx_l_zx.is_strict, y * x, y_prime * x);
    }

    // [x] p(x) <= q(x) where value(p) > value(q)
    //     ==> q <= value(q) => p <= value(q)
    // 
    // for strict?
    //     p(x) < q(x) where value(p) >= value(q)
    //     ==> value(p) <= p => value(p) < q

    bool inf_saturate::try_tangent(pvar v, conflict& core, inequality const& c) {   
        set_rule("[x] p(x) <= q(x) where value(p) > value(q)");
        if (c.is_strict)
            return false;
        if (!c.src->contains_var(v))
            return false;
        if (c.lhs.is_val() || c.rhs.is_val())
            return false;

        pdd q_l(c.lhs), e_l(c.lhs), q_r(c.rhs), e_r(c.rhs);
        bool is_linear = true;
        is_linear &= c.lhs.degree(v) <= 1;
        is_linear &= c.rhs.degree(v) <= 1;
        if (c.lhs.degree(v) == 1) {
            c.lhs.factor(v, 1, q_l, e_l); 
            is_linear &= q_l.is_val();
        }
        if (c.rhs.degree(v) == 1) {
            c.rhs.factor(v, 1, q_r, e_r);
            is_linear &= q_r.is_val();
        }
        if (is_linear)
            return false;

        if (!c.as_signed_constraint().is_currently_false(s))
            return false;
        rational l_val, r_val;
        if (!s.try_eval(c.lhs, l_val))
            return false;
        if (!s.try_eval(c.rhs, r_val))
            return false;
        SASSERT(c.is_strict || l_val > r_val);
        SASSERT(!c.is_strict || l_val >= r_val);
        m_new_constraints.reset();
        m_new_constraints.push_back(c.as_signed_constraint());
        if (c.is_strict) {
            auto d = s.ule(l_val, c.lhs);
            if (d.bvalue(s) == l_false) // it is a different value conflict that contains v
                return false;
            m_new_constraints.push_back(d);
            auto conseq = s.ult(r_val, c.rhs);
            return propagate("tangent (strict)", core, c, c, conseq);
        }
        else {
            auto d = s.ule(c.rhs, r_val);
            if (d.bvalue(s) == l_false) // it is a different value conflict that contains v
                return false;
            m_new_constraints.push_back(d);
            auto conseq = s.ule(c.lhs, r_val);
            return propagate("tangent (non-strict)", core, c, c, conseq);
        }
    }

}
