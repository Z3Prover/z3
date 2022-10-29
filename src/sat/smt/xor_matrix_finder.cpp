#include "sat/smt/xor_matrix_finder.h"
#include "sat/smt/xor_solver.h"


namespace xr {

    xor_matrix_finder::xor_matrix_finder(solver& s) : m_xor(s), m_sat(s.s()) { }
        
    inline bool xor_matrix_finder::belong_same_matrix(const constraint& x) {
        uint32_t comp_num = -1;
        for (sat::bool_var v : x) {
            if (m_table[v] == l_undef) 
                //Belongs to none, abort
                return false;            
            if (comp_num == -1) 
                //Belongs to this one
                comp_num = m_table[v];            
            else if (comp_num != m_table[v]) 
                //Another var in this XOR belongs to another component
                return false;            
        }
        return true;
    }
    
    bool xor_matrix_finder::find_matrices(bool& can_detach) {

        SASSERT(!m_sat.inconsistent());
#if 0
        SASSERT(m_solver->gmatrices.empty());
        can_detach = true;
    
        m_table.clear();
        m_table.resize(m_solver->nVars(), l_undef);
        m_reverseTable.clear();
        clash_vars_unused.clear();
        m_matrix_no = 0;
        
        XorFinder finder(NULL, solver);
    
        for(auto& x: m_solver->xorclauses_unused) m_solver->xorclauses.push_back(std::move(x));
        m_solver->xorclauses_unused.clear();
        m_solver->clauseCleaner->clean_xor_clauses(solver->xorclauses);
    
        finder.grab_mem();
        finder.move_xors_without_connecting_vars_to_unused();
        if (!finder.xor_together_xors(m_solver->xorclauses)) return false;
    
        finder.move_xors_without_connecting_vars_to_unused();
        finder.clean_equivalent_xors(m_solver->xorclauses);
        for(const auto& x: m_solver->xorclauses_unused)
            clash_vars_unused.insert(x.clash_vars.begin(), x.clash_vars.end());
    
        if (m_solver->xorclauses.size() < m_solver->conf.gaussconf.min_gauss_xor_clauses) {
            can_detach = false;
            return true;
        }
    
        //Just one giant matrix.
        if (!m_solver->conf.gaussconf.doMatrixFind) {
            m_solver->gmatrices.push_back(new EGaussian(m_solver, 0, m_solver->xorclauses));
            m_solver->gqueuedata.resize(m_solver->gmatrices.size());
            return true;
        }
    
        std::vector<uint32_t> newSet;
        set<uint32_t> tomerge;
        for (const constraint& x : m_solver->m_constraints) {
            if (belong_same_matrix(x))
                continue;
    
            tomerge.clear();
            newSet.clear();
            for (uint32_t v : x) {
                if (m_table[v] != l_undef)
                    tomerge.insert(m_table[v]);
                else
                    newSet.push_back(v);
            }
            if (tomerge.size() == 1) {
                const uint32_t into = *tomerge.begin();
                auto intoReverse = m_reverseTable.find(into);
                for (uint32_t i = 0; i < newSet.size(); i++) {
                    intoReverse->second.push_back(newSet[i]);
                    m_table[newSet[i]] = into;
                }
                continue;
            }
    
            for (uint32_t v: tomerge) {
                newSet.insert(newSet.end(), m_reverseTable[v].begin(), m_reverseTable[v].end());
                m_reverseTable.erase(v);
            }
            for (uint32_t i = 0; i < newSet.size(); i++)
                m_table[newSet[i]] = m_matrix_no;
            m_reverseTable[m_matrix_no] = newSet;
            m_matrix_no++;
        }
    
        uint32_t numMatrixes = set_matrixes();
    
        const bool time_out =  false;
        
        return !m_solver->inconsistent();
#endif
        return false;
    }
    
    uint32_t xor_matrix_finder::set_matrixes() {

        svector<matrix_shape> matrix_shapes;
        svector<ptr_vector<constraint>> xors_in_matrix(m_matrix_no);

        for (unsigned i = 0; i < m_matrix_no; i++) {
            matrix_shapes.push_back(matrix_shape(i));
            matrix_shapes[i].m_num = i;
            matrix_shapes[i].m_cols = m_reverseTable[i].size();
        }

        for (constraint* x : m_xor.m_constraints) {
            //take 1st variable to check which matrix it's in.
            const uint32_t matrix = m_table[(*x)[0]];
            SASSERT(matrix < m_matrix_no);
    
            //for stats
            matrix_shapes[matrix].m_rows ++;
            matrix_shapes[matrix].m_sum_xor_sizes += x->get_size();
            xors_in_matrix[matrix].push_back(x);
        }
      
        m_xor.m_constraints.clear();
    
        for (auto& m: matrix_shapes) 
            if (m.tot_size() > 0) 
                m.m_density = (double)m.m_sum_xor_sizes / (double)(m.tot_size());
                    
     
        std::sort(matrix_shapes.begin(), matrix_shapes.end(), m_sorter);
    
        uint32_t realMatrixNum = 0;
        uint32_t unusedMatrix = 0;
        uint32_t too_few_rows_matrix = 0;
        uint32_t unused_matrix_printed = 0;
        for (unsigned a = m_matrix_no; a-- > 0; ) {
            matrix_shape& m = matrix_shapes[a];
            uint32_t i = m.m_num;
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
                if (x->is_detached()) {
                    use_matrix = true;
                    break;
                }
            }
    
#if 0
            if (m_sat.get_config().force_use_all_matrixes) {
                use_matrix = true;
            }
#endif
    
#if 0
            if (use_matrix) {
                m_xor.gmatrices.push_back(
                    alloc(EGaussian, m_xor, realMatrixNum, xors_in_matrix[i]));
                m_xor.gqueuedata.resize(m_solver->gmatrices.size());
    
                realMatrixNum++;
                SASSERT(m_solver->gmatrices.size() == realMatrixNum);
            } 
            else {
                for (auto& x: xors_in_matrix[i]) {
                    m_xor.xorclauses_unused.push_back(x);
                    clash_vars_unused.insert(x.clash_vars.begin(), x.clash_vars.end());
                }
                unusedMatrix++;
            }
#endif
        }
        return realMatrixNum;
    }
}
