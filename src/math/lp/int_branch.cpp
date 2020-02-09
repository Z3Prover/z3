/*++
Copyright (c) 2020 Microsoft Corporation

Module Name:

    int_branch.cpp

Abstract:

    Branch heuristic

Author:
    Nikolaj Bjorner (nbjorner)
    Lev Nachmanson (levnach)

Revision History:
--*/

#include "math/lp/int_solver.h"
#include "math/lp/lar_solver.h"
#include "math/lp/int_branch.h"

namespace lp {

    int_branch::int_branch(int_solver& lia):lia(lia), lra(lia.lra) {}

    lia_move int_branch::operator()() {
        int j = find_any_inf_int_column_basis_first();
        return j == -1? lia_move::sat : create_branch_on_column(j);        
    }

    int int_branch::find_any_inf_int_column_basis_first() {
        int j = find_inf_int_base_column();
        return j != -1 ? j : find_inf_int_nbasis_column();
    }

    lia_move int_branch::create_branch_on_column(int j) {
        TRACE("check_main_int", tout << "branching" << std::endl;);
        lp_assert(lia.m_t.is_empty());
        lp_assert(j != -1);
        lia.m_t.add_monomial(mpq(1), lra.adjust_column_index_to_term_index(j));
        if (lia.is_free(j)) {
            lia.m_upper = lia.random() % 2;
            lia.m_k = mpq(0);
        }
        else {
            lia.m_upper = left_branch_is_more_narrow_than_right(j);
            lia.m_k = lia.m_upper? floor(lia.get_value(j)) : ceil(lia.get_value(j));        
        }
        
        TRACE("int_solver",
              lia.display_column(tout << "branching v" << j << " = " << lia.get_value(j) << "\n", j);
              tout << "k = " << lia.m_k << std::endl;);
        return lia_move::branch;        
    }

    bool int_branch::left_branch_is_more_narrow_than_right(unsigned j) {
        switch (lra.m_mpq_lar_core_solver.m_r_solver.m_column_types[j] ) {
        case column_type::fixed:
            return false;
        case column_type::boxed: {
            auto k = floor(lia.get_value(j));
            return k - lia.lower_bound(j).x < lia.upper_bound(j).x - (k + mpq(1));
        }
        case column_type::lower_bound: 
            return true;
        case column_type::upper_bound:
            return false;
        default:
            return false;
        }       
    }

    int int_branch::find_inf_int_base_column() {
        unsigned inf_int_count = 0;
        int j = find_inf_int_boxed_base_column_with_smallest_range(inf_int_count);
        if (j != -1) {
            return j;
        }
        if (inf_int_count == 0)
            return -1;
        unsigned k = lia.random() % inf_int_count;
        return get_kth_inf_int(k);
    }
    
    int int_branch::get_kth_inf_int(unsigned k) const {
        for (unsigned j : lra.r_basis()) 
            if (lia.column_is_int_inf(j) && k-- == 0)
                return j;
        lp_assert(false);
        return -1;
    }
    
    int int_branch::find_inf_int_nbasis_column() const {
        for (unsigned j : lra.r_nbasis())
            if (!lia.column_is_int_inf(j)) {
                return j;    
            }
        return -1; 
    }
    
    int int_branch::find_inf_int_boxed_base_column_with_smallest_range(unsigned & inf_int_count) {
        inf_int_count = 0;
        int result = -1;
        mpq range;
        mpq new_range;
        mpq small_range_thresold(1024);
        unsigned n = 0;
        lar_core_solver & lcs = lra.m_mpq_lar_core_solver;
        
        for (unsigned j : lra.r_basis()) {
            if (!lia.column_is_int_inf(j))
                continue;
            inf_int_count++;
            if (!lia.is_boxed(j))
                continue;
            lp_assert(!lia.is_fixed(j));
            new_range  = lcs.m_r_upper_bounds()[j].x - lcs.m_r_lower_bounds()[j].x;
            if (new_range > small_range_thresold) 
                continue;
            if (result == -1 || new_range < range) {
                result = j;
                range  = new_range;
                n      = 1;
            }
            else if (new_range == range && lia.random() % (++n) == 0) {
                lp_assert(n > 1);
                result = j;
            }
        }
        return result;    
    }
    
}
