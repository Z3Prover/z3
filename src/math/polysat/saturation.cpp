/*++
Copyright (c) 2021 Microsoft Corporation

Module Name:

    Polysat core saturation

Author:

    Nikolaj Bjorner (nbjorner) 2021-03-19
    Jakob Rath 2021-04-6

--*/
#include "math/polysat/saturation.h"
#include "math/polysat/solver.h"
#include "math/polysat/log.h"

namespace polysat {

    constraint_manager& inference_engine::cm() { return s().m_constraints; }

    /** Polynomial superposition between two equalities that contain v.
     */
    bool inf_polynomial_superposition::perform(pvar v, conflict_core& core) {
        // TODO: check superposition into disequality again (see notes)

        // TODO: use indexing/marking for this instead of allocating a temporary vector
        // TODO: core saturation premises are from \Gamma (i.e., has_bvar)... but here we further restrict to the core; might need to revise
        //       -- especially: should take into account results from previous saturations (they will be in \Gamma, but only if we use the constraint or one of its descendants for the lemma)
        //       actually: we want to take one from the current cjust (currently true) and one from the conflict (currently false)
        vector<signed_constraint> candidates;
        for (auto c : core)
            if (c->has_bvar() && c.is_positive() && c->is_eq() && c->contains_var(v))
                candidates.push_back(c);

        LOG_H3("Trying polynomial superposition...");
        for (auto it1 = candidates.begin(); it1 != candidates.end(); ++it1) {
            for (auto it2 = it1 + 1; it2 != candidates.end(); ++it2) {
                signed_constraint c1 = *it1;
                signed_constraint c2 = *it2;
                SASSERT(c1 != c2);
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
                // TODO: we need to track the premises somewhere. also that we need to patch \Gamma if the constraint is used in the lemma.
                // TODO: post-check to make sure r is false under current assignment. otherwise the rule makes no sense.
                vector<signed_constraint> premises;
                premises.push_back(c1);
                premises.push_back(c2);
                core.insert(c, std::move(premises));
                return true;

//             clause_builder clause(m_solver);
//             clause.push_literal(~c1->blit());
//             clause.push_literal(~c2->blit());
//             clause.push_new_constraint(m_solver.m_constraints.eq(lvl, r));
//             return clause.build();
            }
        }

        return false;
    }

}
