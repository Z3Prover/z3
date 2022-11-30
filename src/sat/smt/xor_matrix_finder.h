/*++
Copyright (c) 2022 Microsoft Corporation

Module Name:

    xor_matrix_finder.h

Abstract:

   Based on CMS (crypto minisat by Mate Soos).

--*/

#pragma once

#include "util/debug.h"
#include "util/vector.h"
#include "util/uint_set.h"
#include "util/map.h"
#include "sat/sat_solver.h"
#include "sat/smt/xor_gaussian.h"

namespace xr {

    class solver;
    class constraint;
    
    class xor_matrix_finder {
        
        struct matrix_shape {
            matrix_shape(unsigned matrix_num) : m_num(matrix_num) {}
        
            matrix_shape() {}
        
            unsigned m_num = 0;
            unsigned m_rows = 0;
            unsigned m_cols = 0;
            unsigned m_sum_xor_sizes = 0;
            double m_density = 0;
        
            uint64_t tot_size() const {
                return (uint64_t)m_rows * (uint64_t)m_cols;
            }
        };

        struct sorter {
            bool operator()(const matrix_shape& left, const matrix_shape& right) {
                return left.m_sum_xor_sizes < right.m_sum_xor_sizes;
            }
        };
        
        u_map<unsigned_vector> m_reverseTable; //matrix -> vars
        unsigned_vector        m_table; //var -> matrix
        sorter                 m_sorter;
        solver&                m_xor;
        sat::solver&           m_sat;
        
        
        unsigned set_matrixes(unsigned matrix_no);
        
        inline bool belong_same_matrix(const xor_clause& x);
        
    public:
        xor_matrix_finder(solver& solver);
        
        bool find_matrices(bool& can_detach);
        uint_set clash_vars_unused;
    };
}
