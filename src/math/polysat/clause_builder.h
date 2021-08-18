/*++
Copyright (c) 2021 Microsoft Corporation

Module Name:

    polysat clause builder

Author:

    Jakob Rath 2021-04-6

Notes:

 Builds a clause from literals and constraints.
 Takes care to
 - resolve with unit clauses and accumulate their dependencies,
 - skip trivial new constraints such as "4 <= 1".

--*/
#pragma once
#include "math/polysat/constraint.h"
#include "math/polysat/types.h"

namespace polysat {
  
    class clause_builder {
        solver&               m_solver;
        sat::literal_vector   m_literals;
        constraint_ref_vector m_new_constraints;
        p_dependency_ref      m_dep;
        unsigned              m_level = 0;

    public:
        clause_builder(solver& s);

        bool empty() const { return m_literals.empty() && m_new_constraints.empty() && m_dep == nullptr && m_level == 0; }
        void reset();

        /// Build the clause. This will reset the clause builder so it can be reused.
        clause_ref build();

        void add_dependency(p_dependency* d);

        /// Add a literal to the clause.
        /// Intended to be used for literals representing a constraint that already exists.
        void push_literal(sat::literal lit);
      
        /// Add a constraint to the clause that does not yet exist in the solver so far.
        void push_new_constraint(constraint_literal_ref c);
    };

}
