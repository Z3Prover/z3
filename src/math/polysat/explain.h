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

    class solver;

    class inference_engine {
    public:
        virtual ~inference_engine() {}
        /** Try to apply an inference rule. Returns true if a new constraint was added to the core. */
        virtual bool perform(conflict_explainer& ce) = 0;
    };

    class inf_polynomial_superposition : public inference_engine {
    public:
        bool perform(conflict_explainer& ce) override;
    };

    // TODO: other rules
    // clause_ref by_ugt_x();
    // clause_ref by_ugt_y();
    // clause_ref by_ugt_z();
    // clause_ref y_ule_ax_and_x_ule_z();

    class conflict_explainer {
        solver& m_solver;

        conflict_core m_conflict;

        scoped_ptr_vector<inference_engine> inference_engines;

        bool push_omega_mul(clause_builder& clause, unsigned level, unsigned p, pdd const& x, pdd const& y);
    public:
        /** Create empty conflict */
        conflict_explainer(solver& s);

        /** Perform one step of core saturation, if possible.
         *  Core saturation derives new constraints according applicable inference rules.
         */
        bool saturate();

        /** resolve conflict state against assignment to v */
        void resolve(pvar v, ptr_vector<constraint> const& cjust_v);
        void resolve(sat::literal lit);

        // TODO: move conflict resolution from solver into this class.
        //       we have a single public method as entry point to conflict resolution.
        //       what do we need to return?

        /** conflict resolution until first (relevant) decision */
        void resolve();
    };
}
