#if 0
/*++
Copyright (c) 2021 Microsoft Corporation

Module Name:

    Conflict explanation

Author:

    Nikolaj Bjorner (nbjorner) 2021-03-19
    Jakob Rath 2021-04-6

--*/
#include "math/polysat/eq_explain.h"
#include "math/polysat/solver.h"

namespace polysat {

    
    /**
     * a*v = 0 => a*2^j = 0 or v*2^k = 0
     * for j + k < K
     *
     * az = trailing_zeros(a)
     * a << (K - az - 1) = 0 or v << az = 0
     * 
     */
    bool eq_explain::explain_zero(pvar v, pdd & a, pdd & b, signed_constraint c, conflict& core) {
        pdd bv = s.subst(b);
        if (!bv.is_zero())
            return false;
        rational av = s.subst(a).val();
        SASSERT(!av.is_zero());
        unsigned K = a.power_of_2();
        unsigned az = av.trailing_zeros();
        SASSERT(az < K);
        core.reset();
        core.insert(c);
        core.propagate(s.eq(b));
        core.propagate(~s.eq(a.shl(K - az - 1)));
        core.propagate(~s.eq(b.shl(az)));
        core.log_inference("explain_zero");
        return true;
    }

    bool eq_explain::try_explain1(pvar v, signed_constraint c, conflict& core) {
        if (!c.is_eq())
            return false;
        if (!c.is_currently_false(s))
            return false;
        auto p = c->to_ule().lhs();
        unsigned deg = p.degree(v);
        if (deg != 1)
            return false;
        auto& m = p.manager();
        pdd a = m.zero(), b = m.zero();
        p.factor(v, 1, a, b);
        if (explain_zero(v, a, b, c, core))
            return true;
       
        return false;
    }

    bool eq_explain::try_explain(pvar v, conflict& core) {
        for (auto c : core) 
            if (try_explain1(v, c, core))
                return true;
        return false;
    }

}
#endif
