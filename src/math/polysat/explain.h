/*++
Copyright (c) 2021 Microsoft Corporation

Module Name:

    Conflict explanation / resolution

Author:

    Nikolaj Bjorner (nbjorner) 2021-03-19
    Jakob Rath 2021-04-6

--*/
#pragma once
#include "math/polysat/constraint.h"
#include "math/polysat/clause_builder.h"
#include "math/polysat/interval.h"
#include "math/polysat/solver.h"

namespace polysat {

    // TODO: later, we probably want to update this class incrementally (adding/removing constraints as we go back through the trail)
    // TODO: indexing of constraints/clauses?
    class conflict_explainer {
        solver& m_solver;
        constraints_and_clauses m_conflict;
        pvar m_var = null_var;
        ptr_vector<constraint> m_cjust_v;


        clause_ref by_polynomial_superposition();

        clause_ref by_ugt_x();
        clause_ref by_ugt_y();
        clause_ref by_ugt_z();

        clause_ref y_ule_ax_and_x_ule_z();

        p_dependency_ref null_dep() const { return m_solver.mk_dep_ref(null_dependency); }
        bool push_omega_mul(clause_builder& clause, unsigned level, unsigned p, pdd const& x, pdd const& y);
    public:
        conflict_explainer(solver& s, constraints_and_clauses const& conflict);

        clause_ref resolve(pvar v, ptr_vector<constraint> const& cjust_v);
    };
}
