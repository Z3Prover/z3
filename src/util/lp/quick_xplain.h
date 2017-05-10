/*
Copyright (c) 2017 Microsoft Corporation
Author: Lev Nachmanson
*/

#pragma once
#include "util/vector.h"
#include <unordered_set>

namespace lean {
    class lar_solver; // forward definition
   
    class quick_xplain {
        std::unordered_set<unsigned> m_x; // the minimal set of constraints, the core - it is empty at the begining
        vector<lar_constraint> m_constraints_in_local_vars;
        vector<std::pair<mpq, constraint_index>> & m_explanation;
        const lar_solver& m_parent_solver;
        lar_solver & m_qsol;
        vector<constraint_index> m_local_constraint_offset_to_external_ci;
        std::unordered_map<constraint_index, unsigned> m_local_ci_to_constraint_offsets;
        quick_xplain(vector<std::pair<mpq, constraint_index>> & explanation, const lar_solver & parent_lar_solver, lar_solver & qsol);
        void minimize(const vector<unsigned> & u);
        void add_constraint_to_qsol(unsigned j);
        void copy_constraint_and_add_constraint_vars(const lar_constraint& lar_c);
        void copy_constraints_to_local_constraints();
        bool infeasible();
        bool is_feasible(const vector<unsigned> & x, unsigned k) const;
        bool x_is_minimal() const;
    public:
        static void run(vector<std::pair<mpq, constraint_index>> & explanation,const lar_solver & ls);
        void solve();
    };
}
