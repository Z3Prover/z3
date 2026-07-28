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
    lra.move_non_basic_columns_to_bounds();
    int j = find_inf_int_base_column();
    return j == -1? lia_move::sat : create_branch_on_column(j);        
}

lia_move int_branch::create_branch_on_column(int j) {
    TRACE(check_main_int, tout << "branching" << std::endl;);
    lia.get_term().clear();

    SASSERT(j != -1);
    lia.get_term().add_monomial(mpq(1), j);
    if (lia.is_free(j)) {
        lia.is_upper() = lia.settings().random_next() % 2;
        lia.offset() = mpq(0);
    }
    else {
        lia.is_upper() = lia.settings().random_next() % 2;
        lia.offset() = lia.is_upper()? floor(lia.get_value(j)) : ceil(lia.get_value(j));        
    }
        
    TRACE(int_solver,
          lia.display_column(tout << "branching v" << j << " = " << lia.get_value(j) << "\n", j);
          tout << "k = " << lia.offset() << std::endl;);
    return lia_move::branch;        
}


int int_branch::find_inf_int_base_column() {
    int r_small_box = -1;
    int r_small_value = -1;
    int r_any_value = -1;
    unsigned n_small_box = 1;
    unsigned n_small_value = 1;
    unsigned n_any_value = 1;
    mpq range;
    mpq new_range;
    mpq small_value(1024);
    mpq min_any_value;
    unsigned prev_usage = 0;

    auto add_column = [&](bool improved, int &result, unsigned &n, unsigned j) {
        if (result == -1)
            result = j;
        else if (improved && ((random() % (++n)) == 0))
            result = j;
    };

    for (unsigned j : lra.r_basis()) {
        if (!lia.column_is_int_inf(j))
            continue;
        if (lia.settings().get_cancel_flag()) {
            return -1;
        }
        SASSERT(!lia.is_fixed(j));

        unsigned usage = lra.usage_in_terms(j);
        if (lia.is_boxed(j) && (new_range = lra.bound_span_x(j) - rational(2 * usage)) <= small_value) {
            bool improved = new_range <= range || r_small_box == -1;
            if (improved)
                range = new_range;
            add_column(improved, r_small_box, n_small_box, j);
            continue;
        }
        impq const &value = lia.get_value(j);
        if (abs(value.x) < small_value || (lra.column_has_upper_bound(j) && small_value > lia.upper_bound(j).x - value.x) ||
            (lia.has_lower(j) && small_value > value.x - lia.lower_bound(j).x)) {
            TRACE(int_solver, tout << "small j" << j << "\n");
            add_column(true, r_small_value, n_small_value, j);
            continue;
        }
        TRACE(int_solver, tout << "any j" << j << "\n");
        // Among columns with a large value, prefer the one whose
        // absolute value is smallest to avoid branching on ever
        // larger integers when better (smaller) options are available.
        mpq const abs_value = abs(value.x);
        if (r_any_value == -1 || abs_value < min_any_value) {
            r_any_value = j;
            min_any_value = abs_value;
            n_any_value = 1;
            prev_usage = usage;
        }
        else if (abs_value == min_any_value) {
            add_column(usage >= prev_usage, r_any_value, n_any_value, j);
            if (usage > prev_usage)
                prev_usage = usage;
        }
    }

    if (r_small_box != -1 && (lra.settings().random_next() % 3 != 0))
        return r_small_box;
    if (r_small_value != -1 && (lra.settings().random_next() % 3) != 0)
        return r_small_value;
    if (r_any_value != -1)
        return r_any_value;
    if (r_small_box != -1)
        return r_small_box;
    return r_small_value;

}
   
}
