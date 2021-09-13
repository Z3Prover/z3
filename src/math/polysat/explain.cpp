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
        SASSERT(c1.is_currently_true(s()));
        SASSERT(c2.is_currently_false(s()));
        LOG_H3("Resolving upon v" << v);
        LOG("c1: " << c1);
        LOG("c2: " << c2);
        pdd a = c1->to_ule().p();
        pdd b = c2->to_ule().p();
        pdd r = a;
        if (!a.resolve(v, b, r) && !b.resolve(v, a, r))
            return {};
        // Only keep result if the degree in c2 was reduced.
        // (this condition might be too strict, but we use it for now to prevent looping)
        if (b.degree(v) <= r.degree(v))
            return {};
        signed_constraint c = s().eq(r);
        LOG("resolved: " << c << "        currently false? " << c.is_currently_false(s()));
        if (!c.is_currently_false(s()))
            return {};
        return c;
    }

    bool ex_polynomial_superposition::is_positive_equality_over(pvar v, signed_constraint const& c) {
        return c.is_positive() && c->is_eq() && c->contains_var(v);
    }

    // c2 ... constraint that is currently false
    // Try to replace it with a new false constraint (derived from superposition with a true constraint)
    signed_constraint ex_polynomial_superposition::find_replacement(signed_constraint c2, pvar v, conflict_core& core) {
        for (auto c1 : core) {
            if (!is_positive_equality_over(v, c1))
                continue;
            if (!c1.is_currently_true(s()))
                continue;

            signed_constraint c = resolve1(v, c1, c2);
            if (!c)
                continue;
            vector<signed_constraint> premises;
            premises.push_back(c1);
            premises.push_back(c2);
            core.replace(c2, c, std::move(premises));
            return c;
        }
        return {};
    }

    // TODO(later): check superposition into disequality again (see notes)
    // true = done, false = abort, undef = continue
    lbool ex_polynomial_superposition::try_explain1(pvar v, conflict_core& core) {
        for (auto c2 : core) {
            if (!is_positive_equality_over(v, c2))
                continue;
            if (!c2.is_currently_false(s()))
                continue;

            // TODO: can try multiple replacements at once; then the c2 loop needs to be done only once... (requires some reorganization for storing the premises)
            signed_constraint c = find_replacement(c2, v, core);
            if (!c)
                continue;

            if (!c->contains_var(v)) {
                core.keep(c);
                core.remove_var(v);
                return l_true;
            }
            else
                return l_undef;
        }
        return l_false;
    }

    bool ex_polynomial_superposition::try_explain(pvar v, conflict_core& core) {
        LOG_H3("Trying polynomial superposition...");
        lbool result = l_undef;
        while (result == l_undef)
            result = try_explain1(v, core);
        LOG("success? " << result);
        return result;
    }

}
