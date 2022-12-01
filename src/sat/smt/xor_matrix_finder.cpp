/*++
Copyright (c) 2022 Microsoft Corporation

Module Name:

    xor_matrix_finder.cpp

Abstract:

   Based on CMS (crypto minisat by Mate Soos).

Notes:
- if use-matrices is false, maybe just disable xor? That is don't support dual approach

--*/


#include "sat/sat_xor_finder.h"
#include "sat/smt/xor_matrix_finder.h"
#include "sat/smt/xor_solver.h"

namespace xr {

    xor_matrix_finder::xor_matrix_finder(solver& s) : m_xor(s), m_sat(s.s()) { }
        
    inline bool xor_matrix_finder::belong_same_matrix(const xor_clause& x) {
        unsigned comp_num = -1;
        for (sat::bool_var v : x) {
            if (m_table[v] == (unsigned)-1) // Belongs to none, abort
                return false;            
            if (comp_num == -1) // Belongs to this one                
                comp_num = m_table[v];            
            else if (comp_num != m_table[v]) // Another var in this XOR belongs to another component                
                return false;            
        }
        // All variables in the xor clause belongs to the same matrix
        return true;
    }
    
    bool xor_matrix_finder::find_matrices(bool& can_detach) {

        SASSERT(!m_sat.inconsistent());
        SASSERT(m_xor.m_gmatrices.empty());
        
        can_detach = true;
        
        clash_vars_unused.reset();
        
        for (auto& x: m_xor.m_xorclauses_unused) 
            m_xor.m_xorclauses.push_back(x);
        m_xor.m_xorclauses_unused.clear();
        m_xor.clean_xor_clauses(m_xor.m_xorclauses); 
    
        m_xor.move_xors_without_connecting_vars_to_unused();
        if (!m_xor.xor_together_xors(m_xor.m_xorclauses)) 
            return false;
    
        m_xor.move_xors_without_connecting_vars_to_unused();
        m_xor.clean_equivalent_xors(m_xor.m_xorclauses);
        for (const auto& c : m_xor.m_xorclauses_unused){
            for (const auto& v : c) {
                clash_vars_unused.insert(v);                
            }
        }
    
        if (m_xor.m_xorclauses.size() < m_sat.get_config().m_xor_gauss_min_clauses) {
            can_detach = false;
            return true;
        }
    
        //Just one giant matrix.
        if (!m_sat.get_config().m_xor_gauss_doMatrixFind) {
            m_xor.m_gmatrices.push_back(alloc(EGaussian, m_xor, 0, m_xor.m_xorclauses));
            m_xor.m_gqueuedata.resize(m_xor.m_gmatrices.size());
            return true;
        }
    
        // Assign xor constraints to (multiple) gaussian matrixes
        // If two xor clauses share variables, the clauses have to be together in at least one matrix
        bool_var_vector newSet;
        uint_set to_merge;
        unsigned matrix_no = 0;
        
        m_table.clear();
        m_table.resize(m_sat.num_vars(), (unsigned)-1);
        m_reverseTable.reset();
        
        for (const xor_clause& x : m_xor.m_xorclauses) {
            
            if (belong_same_matrix(x))
                continue;
    
            to_merge.reset();
            newSet.clear();
            for (bool_var v : x) {
                if (m_table[v] != (unsigned)-1)
                    to_merge.insert(m_table[v]);
                else
                    newSet.push_back(v);
            }
            if (to_merge.num_elems() == 1) {
                unsigned into = *to_merge.begin();
                unsigned_vector& intoReverse = m_reverseTable[into];
                for (unsigned i = 0; i < newSet.size(); i++) {
                    intoReverse.push_back(newSet[i]);
                    m_table[newSet[i]] = into;
                }
                continue;
            }
    
            for (unsigned v: to_merge) {
                for (const auto& v2 : m_reverseTable[v])
                    newSet.insert(v2);
                m_reverseTable.erase(v);
            }
            for (auto j : newSet)
                m_table[j] = matrix_no;
            m_reverseTable.insert(matrix_no++, newSet);
        }
    
        set_matrixes(matrix_no);

        return !m_sat.inconsistent();
    }
    
    unsigned xor_matrix_finder::set_matrixes(unsigned matrix_no) {

        svector<matrix_shape> matrix_shapes;
        vector<vector<xor_clause>> xors_in_matrix(matrix_no);

        for (unsigned i = 0; i < matrix_no; i++) {
            matrix_shapes.push_back(matrix_shape(i));
            matrix_shapes[i].m_num = i;
            matrix_shapes[i].m_cols = m_reverseTable[i].size();
        }

        for (xor_clause& x : m_xor.m_xorclauses) {
            // take 1st variable to check which matrix it's in.
            unsigned matrix = m_table[x[0]];
            SASSERT(matrix < matrix_no);
    
            //for stats
            matrix_shapes[matrix].m_rows ++;
            matrix_shapes[matrix].m_sum_xor_sizes += x.size();
            xors_in_matrix[matrix].push_back(x);
        }
      
        m_xor.m_xorclauses.clear();
        
     
        std::sort(matrix_shapes.begin(), matrix_shapes.end(), m_sorter);
    
        unsigned realMatrixNum = 0;
        unsigned unusedMatrix = 0;
        unsigned too_few_rows_matrix = 0;
        for (unsigned a = matrix_no; a-- > 0; ) {
            matrix_shape& m = matrix_shapes[a];
            unsigned i = m.m_num;
            if (m.m_rows == 0) 
                continue;            
    
            bool use_matrix = true;
    
            // Over- or undersized 
            
            // Too many rows in matrix
            if (use_matrix && m.m_rows > m_sat.get_config().m_xor_gauss_max_matrix_rows) 
                use_matrix = false;
            
            // Too many columns in matrix
            if (use_matrix && m.m_cols > m_sat.get_config().m_xor_gauss_max_matrix_columns) 
                use_matrix = false;
                 
            // Too few rows in matrix
            if (use_matrix && m.m_rows < m_sat.get_config().m_xor_gauss_min_matrix_rows) 
                use_matrix = false, too_few_rows_matrix++;                            
    
            // Over the max number of matrixes
            if (use_matrix && realMatrixNum >= m_sat.get_config().m_xor_gauss_max_num_matrices) 
                use_matrix = false;
                       
            // if already detached, we MUST use the matrix
            for (const auto& x: xors_in_matrix[i]) {
                if (x.m_detached) {
                    use_matrix = true;
                    break;
                }
            }
    
            if (m_sat.get_config().m_xor_gauss_force_use_all_matrices) 
                use_matrix = true;            
    
            if (use_matrix) {
                m_xor.m_gmatrices.push_back(
                    alloc(EGaussian, m_xor, realMatrixNum, xors_in_matrix[i]));
                m_xor.m_gqueuedata.resize(m_xor.m_gmatrices.size());
    
                realMatrixNum++;
                SASSERT(m_xor.m_gmatrices.size() == realMatrixNum);
            } 
            else {
                for (auto& x: xors_in_matrix[i]) {
                    m_xor.m_xorclauses_unused.push_back(x);
                    for (const auto& v : x.m_clash_vars) {
                        clash_vars_unused.insert(v);                        
                    }
                }
                unusedMatrix++;
            }
        }
        return realMatrixNum;
    }
}
