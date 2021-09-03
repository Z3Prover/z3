/*++
Copyright (c) 2021 Microsoft Corporation

Module Name:

    Conflict explanation

Author:

    Nikolaj Bjorner (nbjorner) 2021-03-19
    Jakob Rath 2021-04-6

--*/
#pragma once
#include "math/polysat/conflict_core.h"
#include "math/polysat/constraint.h"
#include "math/polysat/clause_builder.h"
#include "math/polysat/interval.h"

namespace polysat {


#if 0
    class conflict_explainer {
        solver& m_solver;

        // conflict_core m_conflict;
        vector<constraint> m_new_assertions;  // to be inserted into Gamma (conclusions from saturation)

        scoped_ptr_vector<inference_engine> inference_engines;

        bool push_omega_mul(clause_builder& clause, unsigned level, unsigned p, pdd const& x, pdd const& y);

        // Gamma
        // search_state& search() { return m_solver.m_search; }
        // Core
        // conflict_core& conflict() { return m_solver.m_conflict; }
    public:
        /** Create empty conflict */
        conflict_explainer(solver& s);

        /** Perform one step of core saturation, if possible.
         *  Core saturation derives new constraints according applicable inference rules.
         */
        bool saturate();

        /** resolve conflict state against assignment to v */
        void resolve(pvar v, ptr_vector<constraint> const& cjust_v);  // TODO: try variable elimination of 'v', if not possible, core saturation and core reduction. (actually reduction could be one specific VE method).
        void resolve(sat::literal lit);

        // TODO: move conflict resolution from solver into this class.
        //       we have a single public method as entry point to conflict resolution.
        //       what do we need to return?

        /** conflict resolution until first (relevant) decision */
        void resolve();
    };
#endif
}
