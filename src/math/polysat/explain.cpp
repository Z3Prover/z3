/*++
Copyright (c) 2021 Microsoft Corporation

Module Name:

    Conflict explanation / resolution

Author:

    Nikolaj Bjorner (nbjorner) 2021-03-19
    Jakob Rath 2021-04-6

--*/
#include "math/polysat/explain.h"
#include "math/polysat/log.h"
#include "math/polysat/solver.h"

namespace polysat {

    signed_constraint ex_polynomial_superposition::resolve1(pvar v, signed_constraint c1, signed_constraint c2) {
        // c1 is true, c2 is false
        SASSERT(c1.is_currently_true(s));
        SASSERT(c2.is_currently_false(s));
        LOG_H3("Resolving upon v" << v);
        LOG("c1: " << c1);
        LOG("c2: " << c2);
        pdd a = c1.eq();
        pdd b = c2.eq();
        pdd r = a;
        if (!a.resolve(v, b, r) && !b.resolve(v, a, r))
            return {};
        // Only keep result if the degree in c2 was reduced.
        // (this condition might be too strict, but we use it for now to prevent looping)
        if (b.degree(v) <= r.degree(v))
            return {};
        signed_constraint c = s.eq(r);
        LOG("resolved: " << c << "        currently false? " << c.is_currently_false(s));
        if (!c.is_currently_false(s))
            return {};
        return c;
    }


    // c2 ... constraint that is currently false
    // Try to replace it with a new false constraint (derived from superposition with a true constraint)
    lbool ex_polynomial_superposition::find_replacement(signed_constraint c2, pvar v, conflict& core) {
        vector<signed_constraint> premises;

        for (auto si : s.m_search) {
            if (!si.is_boolean())
                continue;
            auto c1 = s.lit2cnstr(si.lit());       
            if (!c1->contains_var(v))
                continue;
            if (!c1.is_eq())
                continue;
            if (!c1.is_currently_true(s))
                continue;
            signed_constraint c = resolve1(v, c1, c2);
            if (!c)
                continue;
            if (!c->has_bvar())
                s.m_constraints.ensure_bvar(c.get());

            switch (c.bvalue(s)) {
            case l_false:
                // new conflict state based on propagation and theory conflict
                core.reset();
                core.insert(c1);
                core.insert(c2);
                core.insert(~c);
                return l_true;
            case l_undef:
                // Ensure that c is assigned and justified                    
                premises.push_back(c1);
                premises.push_back(c2);
                core.replace(c2, c, premises);
                SASSERT(l_true == c.bvalue(s));
                SASSERT(c.is_currently_false(s));
                break;
            default:
                break;
            }

            // NOTE: more variables than just 'v' might have been removed here (see polysat::test_p3).
            // c alone (+ variables) is now enough to represent the conflict.
            core.reset();
            core.set(c);
            return c->contains_var(v) ? l_undef : l_true;
        }
        return l_false;
    }

    // TODO(later): check superposition into disequality again (see notes)
    // true = done, false = abort, undef = continue
    // TODO: can try multiple replacements at once; then the c2 loop needs to be done only once... (requires some reorganization for storing the premises)
    lbool ex_polynomial_superposition::try_explain1(pvar v, conflict& core) {
        for (auto c2 : core) {
            if (!c2->contains_var(v))
                continue;
            if (!c2.is_eq())
                continue;
            if (!c2.is_currently_false(s))
                continue;
            switch (find_replacement(c2, v, core)) {
            case l_undef:
                return l_undef;
            case l_true:
                return l_true;
            case l_false:
                continue;
            }
        }
        return l_false;
    }

    void ex_polynomial_superposition::reduce_by(pvar v, conflict& core) {
        bool progress = true;
        while (progress) {
            progress = false;
            for (auto c : core) {
                if (!c->contains_var(v))
                    continue;
                if (!c.is_eq())
                    continue;
#if 0
                if (!c.is_currently_true(s))
                    continue;
#endif

                if (!reduce_by(v, c, core))
                    continue;
                progress = true;
                break;                
            }
        }
    }

    bool ex_polynomial_superposition::reduce_by(pvar v, signed_constraint eq, conflict& core) {
        pdd p = eq.eq();
        LOG("using v" << v << " " << eq);
        for (auto c : core) {
            if (c == eq)
                continue;
            if (!c->contains_var(v))
                continue;
            if (c.is_eq())
                continue;
            LOG("try-reduce: " << c << " " << c.is_currently_false(s));
#if 0
            if (!c.is_currently_false(s))
                continue;
#endif
            if (!c->is_ule())
                continue;
            auto lhs = c->to_ule().lhs();
            auto rhs = c->to_ule().rhs();
            auto a = lhs.reduce(v, p);
            auto b = rhs.reduce(v, p);
            if (a == lhs && b == rhs)
                continue;
            auto c2 = s.ule(a, b);
            if (!c.is_positive())
                c2 = ~c2;
            if (!c2.is_currently_false(s))
                continue;
            SASSERT(c2.is_currently_false(s));
            if (!c2->has_bvar() || l_undef == c2.bvalue(s))
                core.keep(c2);  // adds propagation of c to the search stack
            core.reset();
            LOG_H3("Polynomial superposition " << eq << " " << c << " reduced to " << c2);
            if (c2.bvalue(s) == l_false) {
                core.insert(eq);
                core.insert(c);
                core.insert(~c2);
                return false;
            }
            core.set(c2);
            return true;
        }
        return false;
    }

    bool ex_polynomial_superposition::try_explain(pvar v, conflict& core) {
        reduce_by(v, core);
        lbool result = l_undef;
        while (result == l_undef)
            result = try_explain1(v, core);
        return result == l_true;
    }

}
