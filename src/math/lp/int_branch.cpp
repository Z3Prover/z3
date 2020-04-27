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
        lia.m_upper = lia.random() % 2;
        lia.m_k = lia.m_upper? floor(lia.get_value(j)) : ceil(lia.get_value(j));        
    }
        
    TRACE("int_solver",
          lia.display_column(tout << "branching v" << j << " = " << lia.get_value(j) << "\n", j);
          tout << "k = " << lia.m_k << std::endl;);
    return lia_move::branch;        
}

    
int int_branch::find_inf_int_nbasis_column() const {
    unsigned n = 0;
    int r = -1;
    for (unsigned j : lra.r_nbasis()) {
        SASSERT(!lia.column_is_int_inf(j) || !lia.is_fixed(j));
        if (lia.column_is_int_inf(j)) {
            if (n == 0) {
                r = j;
                n = 1;                    
            } else if (lia.random() % (++n) == 0) {
                r = j;
            }
        }
    }
    return r; 
}
    
int int_branch::find_inf_int_base_column() {
    int result = -1;
    mpq range;
    mpq new_range;
    mpq small_range_thresold(1024);
    unsigned n = 0;
    lar_core_solver & lcs = lra.m_mpq_lar_core_solver;
    bool small = false;
    for (unsigned j : lra.r_basis()) {
        SASSERT(!lia.column_is_int_inf(j) || !lia.is_fixed(j));
        if (!lia.column_is_int_inf(j))
            continue;
        bool boxed = lia.is_boxed(j);
        if (small) {
            if (!boxed)
                continue;
            new_range  = lcs.m_r_upper_bounds()[j].x - lcs.m_r_lower_bounds()[j].x;
            if (new_range <= small_range_thresold) {
                if (new_range < range) {
                    n = 1;
                    result = j;
                    range = new_range;
                } else if (new_range == range && lia.random() % (++n) == 0) {
                    result = j;                    
                }
            }
        } else if (boxed &&
                   (range = lcs.m_r_upper_bounds()[j].x - lcs.m_r_lower_bounds()[j].x)
                   <= small_range_thresold) {
            small = true;
            result = j;
            n = 1;
        } else if (result == -1) {
            result = j;
            n      = 1;
        } else if (lia.random() % (++n) == 0) {
            result = j;
        }
    }
    return result;    
}
    
}
