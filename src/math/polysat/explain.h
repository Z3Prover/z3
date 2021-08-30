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

    class conflict_explainer {
        solver& m_solver;

        pvar m_var = null_var;
        ptr_vector<constraint> m_cjust_v;

        // TODO: instead of listing methods, create an abstract class for explanation methods, register them in a vector and call them in turn
        /* Conflict explanation methods */
        clause_ref by_polynomial_superposition();
        clause_ref by_ugt_x();
        clause_ref by_ugt_y();
        clause_ref by_ugt_z();
        clause_ref y_ule_ax_and_x_ule_z();

        p_dependency_ref null_dep();
        // p_dependency_ref null_dep() const { return m_solver.mk_dep_ref(null_dependency); }
        bool push_omega_mul(clause_builder& clause, unsigned level, unsigned p, pdd const& x, pdd const& y);

    public:
        /** Create empty conflict */
        conflict_explainer(solver& s);

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
