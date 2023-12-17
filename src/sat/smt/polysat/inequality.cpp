/*++
Copyright (c) 2021 Microsoft Corporation

Module Name:

    Polysat inequalities

Author:

    Nikolaj Bjorner (nbjorner) 2021-03-19
    Jakob Rath 2021-04-6



--*/
#include "sat/smt/polysat/core.h"
#include "sat/smt/polysat/inequality.h"
#include "sat/smt/polysat/ule_constraint.h"


namespace polysat {


    inequality inequality::from_ule(core& c, constraint_id id) {
        auto src = c.get_constraint(id);
        ule_constraint const& ule = src.to_ule();
        if (src.is_positive())
            return inequality(c, id, ule.lhs(), ule.rhs(), src);
        else
            return inequality(c, id, ule.rhs(), ule.lhs(), src);
    }


#if 0


    bool saturation::verify_Y_l_AxB(pvar x, inequality const& i, pdd const& y, pdd const& a, pdd& b) {
        return i.lhs() == y && i.rhs() == a * c.var(x) + b;
    }


    /**
     * Match [x] a*x + b <= y, val(y) = 0
     */
    bool saturation::is_AxB_eq_0(pvar x, inequality const& i, pdd& a, pdd& b, pdd& y) {
        y.reset(i.rhs().manager());
        y = i.rhs();
        rational y_val;
        if (!c.try_eval(y, y_val) || y_val != 0)
            return false;
        return i.lhs().degree(x) == 1 && (i.lhs().factor(x, 1, a, b), true);
    }

    bool saturation::verify_AxB_eq_0(pvar x, inequality const& i, pdd const& a, pdd const& b, pdd const& y) {
        return y.is_val() && y.val() == 0 && i.rhs() == y && i.lhs() == a * c.var(x) + b;
    }

    bool saturation::is_AxB_diseq_0(pvar x, inequality const& i, pdd& a, pdd& b, pdd& y) {
        if (!i.is_strict())
            return false;
        y.reset(i.lhs().manager());
        y = i.lhs();
        if (i.rhs().is_val() && i.rhs().val() == 1)
            return false;
        rational y_val;
        if (!c.try_eval(y, y_val) || y_val != 0)
            return false;
        a.reset(i.rhs().manager());
        b.reset(i.rhs().manager());
        return i.rhs().degree(x) == 1 && (i.rhs().factor(x, 1, a, b), true);
    }

    /**
     * Match [coeff*x] coeff*x*Y where x is a variable
     */
    bool saturation::is_coeffxY(pdd const& x, pdd const& p, pdd& y) {
        pdd xy = x.manager().zero();
        return x.is_unary() && p.try_div(x.hi().val(), xy) && xy.factor(x.var(), 1, y);
    }

    /**
 * Match [v] v*x <= z*x with x a variable
 */
    bool saturation::is_Xy_l_XZ(pvar v, inequality const& i, pdd& x, pdd& z) {
        return is_xY(v, i.lhs(), x) && is_coeffxY(x, i.rhs(), z);
    }

    bool saturation::verify_Xy_l_XZ(pvar v, inequality const& i, pdd const& x, pdd const& z) {
        return i.lhs() == c.var(v) * x && i.rhs() == z * x;
    }


    /**
     * Determine whether values of x * y is non-overflowing.
     */
    bool saturation::is_non_overflow(pdd const& x, pdd const& y) {
        rational x_val, y_val;
        rational bound = x.manager().two_to_N();
        return c.try_eval(x, x_val) && c.try_eval(y, y_val) && x_val * y_val < bound;
    }


    /**
     * Match [z] yx <= zx with x a variable
     */
    bool saturation::is_YX_l_zX(pvar z, inequality const& c, pdd& x, pdd& y) {
        return is_xY(z, c.rhs(), x) && is_coeffxY(x, c.lhs(), y);
    }

    bool saturation::verify_YX_l_zX(pvar z, inequality const& i, pdd const& x, pdd const& y) {
        return i.lhs() == y * x && i.rhs() == c.var(z) * x;
    }

    /**
     * Match [x] xY <= xZ
     */
    bool saturation::is_xY_l_xZ(pvar x, inequality const& c, pdd& y, pdd& z) {
        return is_xY(x, c.lhs(), y) && is_xY(x, c.rhs(), z);
    }

    /**
     * Match xy = x * Y
     */
    bool saturation::is_xY(pvar x, pdd const& xy, pdd& y) {
        return xy.degree(x) == 1 && xy.factor(x, 1, y);
    }

#endif


}
