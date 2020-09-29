/*++
  Copyright (c) 2020 Microsoft Corporation

  Module Name:

  int_branch.cpp

  Abstract:

  Branch heuristic

  Author:
  Lev Nachmanson (levnach)
  Nikolaj Bjorner (nbjorner)

  Revision History:
  --*/

#include "math/lp/int_solver.h"
#include "math/lp/lar_solver.h"
#include "math/lp/int_branch.h"

namespace lp {

int_branch::int_branch(int_solver& lia):lia(lia), lra(lia.lra) {}

lia_move int_branch::operator()() {
    lra.move_non_basic_columns_to_bounds(true);
    int j = find_inf_int_base_column();
    return j == -1? lia_move::sat : create_branch_on_column(j);        
}

lia_move int_branch::create_branch_on_column(int j) {
    TRACE("check_main_int", tout << "branching" << std::endl;);
    lp_assert(lia.m_t.is_empty());
    lp_assert(j != -1);
    lia.m_t.add_monomial(mpq(1), lra.column_to_reported_index(j));
    if (lia.is_free(j)) {
        lia.m_upper = lia.random() % 2;
        lia.m_k = mpq(0);
    }
    else {
        lia.m_upper = lia.random() % 2;
        lia.m_k = lia.m_upper? floor(lia.get_value(j)) : ceil(lia.get_value(j));        
    }
        
    TRACE("int_solver",
          lia.display_column(tout << "branching v" << j << " = " << lia.get_value(j) << "\n", j);
          tout << "k = " << lia.m_k << std::endl;);
    return lia_move::branch;        
}


int int_branch::find_inf_int_base_column() {
    int result = -1;
    mpq range;
    mpq new_range;
    mpq small_range_thresold(1024);
    unsigned n = 0;
    lar_core_solver & lcs = lra.m_mpq_lar_core_solver;
    unsigned prev_usage = 0; // to quiet down the compile
    unsigned k = 0;
    unsigned usage;
    unsigned j;
    // this loop looks for a column with the most usages, but breaks when
    // a column with a small span of bounds is found
    for (; k < lra.r_basis().size(); k++) {
        j = lra.r_basis()[k];
        if (!lia.column_is_int_inf(j))
            continue;
        usage = lra.usage_in_terms(j);
        if (lia.is_boxed(j) &&  (range = lcs.m_r_upper_bounds()[j].x - lcs.m_r_lower_bounds()[j].x - rational(2*usage)) <= small_range_thresold) {
            result = j;
            k++;            
            n = 1;
            break;
        }
        if (n == 0 || usage > prev_usage) {
            result = j;
            prev_usage = usage;
            n = 1;
        } else if (usage == prev_usage && (lia.random() % (++n) == 0)) {
            result = j;
        }
    }
    SASSERT(k == lra.r_basis().size() || n == 1);
    // this loop looks for boxed columns with a small span
    for (; k < lra.r_basis().size(); k++) {
        j = lra.r_basis()[k];
        if (!lia.column_is_int_inf(j) || !lia.is_boxed(j))
            continue;
        SASSERT(!lia.is_fixed(j));
        usage = lra.usage_in_terms(j);
        new_range  = lcs.m_r_upper_bounds()[j].x - lcs.m_r_lower_bounds()[j].x - rational(2*usage);
        if (new_range < range) {
            n = 1;
            result = j;
            range = new_range;
        } else if (new_range == range && (lia.random() % (++n) == 0)) {
            result = j;                    
        }
    }
    return result;    
}
   
}
