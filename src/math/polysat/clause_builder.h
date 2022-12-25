/*++
Copyright (c) 2021 Microsoft Corporation

Module Name:

    polysat clause builder

Author:

    Jakob Rath 2021-04-6

Notes:

 Builds a clause from literals and constraints.
 Skips trivial new constraints such as "4 <= 1".

--*/
#pragma once
#include "math/polysat/clause.h"
#include "math/polysat/constraint.h"
#include "math/polysat/types.h"

namespace polysat {
  
    class clause_builder {
        solver*               m_solver;
        sat::literal_vector   m_literals;
        /// True iff clause contains a literal that is always true
        /// (only this specific case of tautology is covered by this flag)
        bool                  m_is_tautology = false;
        bool                  m_redundant = clause::redundant_default;

    public:
        clause_builder(solver& s);
        clause_builder(clause_builder const& s) = delete;
        clause_builder(clause_builder&& s) = default;
        clause_builder& operator=(clause_builder const& s) = delete;
        clause_builder& operator=(clause_builder&& s) = default;

        bool empty() const { return m_literals.empty() && !m_is_tautology && m_redundant == clause::redundant_default; }
        void reset();

        void set_redundant(bool r) { m_redundant = r; }

        /// Build the clause. This will reset the clause builder so it can be reused.
        /// Returns nullptr if the clause is a tautology and should not be added to the solver.
        clause_ref build();

        /// Insert constraints into the clause.
        void insert(sat::literal lit);
        void insert(signed_constraint c);
        void insert(inequality const& i) { insert(i.as_signed_constraint()); }

        /// Insert constraints into the clause.
        /// If they are not yet on the search stack, add them as evaluated to \b false.
        /// \pre Constraint must be \b false in the current assignment.
        void insert_eval(sat::literal lit);
        void insert_eval(signed_constraint c);
        void insert_eval(inequality const& i) { insert_eval(i.as_signed_constraint()); }

        /// Insert constraints into the clause.
        /// If possible, evaluate them as in insert_eval.
        /// Evaluation might not be possible if not all variables in the constraint are assigned.
        /// \pre Constraint must be \b non-true in the current assignment.
        void insert_try_eval(sat::literal lit);
        void insert_try_eval(signed_constraint lit);

        using const_iterator = decltype(m_literals)::const_iterator;
        const_iterator begin() const { return m_literals.begin(); }
        const_iterator end() const { return m_literals.end(); }
    };

}
