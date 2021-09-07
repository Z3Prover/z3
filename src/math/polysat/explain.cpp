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

    constraint_manager& explainer::cm() { return s().m_constraints; }

    // TODO(later): check superposition into disequality again (see notes)
    bool ex_polynomial_superposition::try_explain(pvar v, /* vector<signed_constraint> const& cjust_v, */ conflict_core& core) {
        // TODO: core saturation premises are from \Gamma (i.e., has_bvar)... but here we further restrict to the core; might need to revise
        //       -- especially: should take into account results from previous saturations (they will be in \Gamma, but only if we use the constraint or one of its descendants for the lemma)
        //       actually: we want to take one from the current cjust (currently true) and one from the conflict (currently false)

        // TODO: resolve multiple times... a single time might not be enough to eliminate the variable.

        LOG_H3("Trying polynomial superposition...");
        for (auto it1 = core.begin(); it1 != core.end(); ++it1) {
            signed_constraint c1 = *it1;
            if (!c1->has_bvar())
                continue;
            if (!c1.is_positive())
                continue;
            if (!c1->is_eq())
                continue;
            if (!c1->contains_var(v))
                continue;
            if (!c1.is_currently_true(s()))
                continue;

            for (auto it2 = core.begin(); it2 != core.end(); ++it2) {
                signed_constraint c2 = *it2;
                if (!c2->has_bvar())
                    continue;
                if (!c2.is_positive())
                    continue;
                if (!c2->is_eq())
                    continue;
                if (!c2->contains_var(v))
                    continue;
                if (!c2.is_currently_false(s()))
                    continue;

                // TODO: separate method for this; then try_explain1 and try_explain* for multi-steps; replace the false constraint in the core.
                // c1 is true, c2 is false
                LOG("c1: " << c1);
                LOG("c2: " << c2);
                pdd a = c1->to_eq().p();
                pdd b = c2->to_eq().p();
                pdd r = a;
                if (!a.resolve(v, b, r) && !b.resolve(v, a, r))
                    continue;
                unsigned const lvl = std::max(c1->level(), c2->level());
                signed_constraint c = cm().eq(lvl, r);
                LOG("resolved: " << c << "        currently false? " << c.is_currently_false(s()));
                if (!c.is_currently_false(s()))
                    continue;
                vector<signed_constraint> premises;
                premises.push_back(c1);
                premises.push_back(c2);
                if (!c->contains_var(v)) {
                    core.reset(); // TODO: doesn't work; this removes the premises as well... / instead: remove the false one.
                    core.insert(c, std::move(premises));
                    return true;
                } else {
                    core.insert(c, std::move(premises));
                }
            }
        }

        return false;
    }





//         DEBUG_CODE({
//             if (lemma) {
//                 LOG("New lemma: " << *lemma);
//                 for (auto* c : lemma->new_constraints()) {
//                     LOG("New constraint: " << show_deref(c));
//                 }
//                 // All constraints in the lemma must be false in the conflict state
//                 for (auto lit : lemma->literals()) {
//                     if (m_solver.m_bvars.value(lit) == l_false)
//                         continue;
//                     SASSERT(m_solver.m_bvars.value(lit) != l_true);
//                     constraint* c = m_solver.m_constraints.lookup(lit.var());
//                     SASSERT(c);
//                     tmp_assign _t(c, lit);
//                     // if (c->is_currently_true(m_solver)) {
//                     //     LOG("ERROR: constraint is true: " << show_deref(c));
//                     //     SASSERT(false);
//                     // }
//                     // SASSERT(!c->is_currently_true(m_solver));
//                     // SASSERT(c->is_currently_false(m_solver));   // TODO: pvar v may not have a value at this point...
//                 }
//             }
//             else {
//                 LOG("No lemma");
//             }
//         });

//         m_var = null_var;
//         m_cjust_v.reset();
//         return lemma;
//     }




}
