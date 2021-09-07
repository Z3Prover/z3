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
  
    // TODO: this is now incorporated in conflict_core
    class clause_builder {
        solver&               m_solver;
        sat::literal_vector   m_literals;
        p_dependency_ref      m_dep;
        unsigned              m_level = 0;

    public:
        clause_builder(solver& s);

        bool empty() const { return m_literals.empty() && m_dep == nullptr && m_level == 0; }
        void reset();

        unsigned level() const { return m_level; }

        /// Build the clause. This will reset the clause builder so it can be reused.
        clause_ref build();

        void add_dependency(p_dependency* d);

        /// Add a literal to the clause.
        /// Intended to be used for literals representing a constraint that already exists.
        void push_literal(sat::literal lit);

        void push(signed_constraint c);
      
        /// Add a constraint to the clause that does not yet exist in the solver so far.
        // void push_new_constraint(signed_constraint c);

        using const_iterator = decltype(m_literals)::const_iterator;
        const_iterator begin() const { return m_literals.begin(); }
        const_iterator end() const { return m_literals.end(); }
    };

}
