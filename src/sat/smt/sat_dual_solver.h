/*++
Copyright (c) 2020 Microsoft Corporation

Module Name:

    sat_dual_solver.h

Abstract:

    Solver for obtaining implicant.

Author:

    Nikolaj Bjorner (nbjorner) 2020-08-25

--*/
#pragma once
#include "sat/sat_solver.h"

namespace sat {

    class dual_solver {
        solver          m_solver;
        literal_vector  m_roots, m_lits, m_core;
        bool_var_vector m_is_tracked;
        unsigned_vector m_tracked_stack;
        unsigned_vector m_ext2var;
        unsigned_vector m_var2ext;
        unsigned_vector m_roots_lim, m_tracked_lim;
        void add_literal(literal lit);

        bool_var ext2var(bool_var v);
        bool_var var2ext(bool_var v);
        literal  ext2lit(literal lit);
        literal  lit2ext(literal lit);
    public:
        dual_solver(reslimit& l);
        void push();
        void pop(unsigned num_scopes);

        /*
        * track model relevancy for variable 
        */
        void track_relevancy(bool_var v);

        /*
        * Add a root clause from the input problem.
        * At least one literal has to be satisfied in every root.
        */
        void add_root(literal lit, unsigned sz, literal const* clause);

        /*
        * Add auxiliary clauses that originate from compiling definitions.
        */
        void add_aux(unsigned sz, literal const* clause);

        /*
        * Extract a minimized subset of relevant literals from a model for s.
        */
        bool operator()(solver const& s);

        literal_vector const& core() const { return m_core; }
    };
}
