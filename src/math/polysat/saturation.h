/*++
Copyright (c) 2021 Microsoft Corporation

Module Name:

    Polysat core saturation

Author:

    Nikolaj Bjorner (nbjorner) 2021-03-19
    Jakob Rath 2021-04-6

--*/
#pragma once
#include "math/polysat/conflict_core.h"

namespace polysat {

    class solver;
    class constraint_manager;

    class inference_engine {
        friend class conflict_core;
        solver* m_solver = nullptr;
        void set_solver(solver& s) { m_solver = &s; }
    protected:
        solver& s() { return *m_solver; }
        constraint_manager& cm();
    public:
        virtual ~inference_engine() {}
        /** Try to apply an inference rule.
         *  Derive new constraints from constraints containing the variable v (i.e., at least one premise must contain v).
         *  Returns true if a new constraint was added to the core.
         */
        virtual bool perform(pvar v, conflict_core& core) = 0;
    };

    class inf_polynomial_superposition : public inference_engine {
    public:
        bool perform(pvar v, conflict_core& core) override;
    };

    // TODO: other rules
    // clause_ref by_ugt_x();
    // clause_ref by_ugt_y();
    // clause_ref by_ugt_z();
    // clause_ref y_ule_ax_and_x_ule_z();
}
