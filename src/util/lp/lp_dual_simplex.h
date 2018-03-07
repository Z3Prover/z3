/*++
Copyright (c) 2017 Microsoft Corporation

Module Name:

    <name>

Abstract:

    <abstract>

Author:

    Lev Nachmanson (levnach)

Revision History:


--*/
#pragma once
#include "util/vector.h"
#include "util/lp/lp_utils.h"
#include "util/lp/lp_solver.h"
#include "util/lp/lp_dual_core_solver.h"
namespace lp {

template <typename T, typename X>
class lp_dual_simplex: public lp_solver<T, X> {
    lp_dual_core_solver<T, X> * m_core_solver;
    vector<T> m_b_copy;
    vector<T> m_low_bounds; // We don't have a convention here that all low bounds are zeros. At least it does not hold for the first stage solver
    vector<column_type> m_column_types_of_core_solver;
    vector<column_type> m_column_types_of_logicals;
    vector<bool>  m_can_enter_basis;
public:
    ~lp_dual_simplex() override {
        if (m_core_solver != nullptr) {
            delete m_core_solver;
        }
    }

    lp_dual_simplex() : m_core_solver(nullptr) {}


    void decide_on_status_after_stage1();

    void fix_logical_for_stage2(unsigned j);

    void fix_structural_for_stage2(unsigned j);

    void unmark_boxed_and_fixed_columns_and_fix_structural_costs();

    void restore_right_sides();

    void solve_for_stage2();

    void fill_x_with_zeros();

    void stage1();

    void stage2();

    void fill_first_stage_solver_fields();

    column_type get_column_type(unsigned j);

    void fill_costs_bounds_types_and_can_enter_basis_for_the_first_stage_solver_structural_column(unsigned j);

    void fill_costs_bounds_types_and_can_enter_basis_for_the_first_stage_solver_logical_column(unsigned j);

    void fill_costs_and_bounds_and_column_types_for_the_first_stage_solver();

    void set_type_for_logical(unsigned j, column_type col_type) {
        this->m_column_types_of_logicals[j - this->number_of_core_structurals()] = col_type;
    }

    void fill_first_stage_solver_fields_for_row_slack_and_artificial(unsigned row,
                                                              unsigned & slack_var,
                                                                     unsigned & artificial);

    void augment_matrix_A_and_fill_x_and_allocate_some_fields();



    void copy_m_b_aside_and_set_it_to_zeros();

    void find_maximal_solution() override;

    T get_column_value(unsigned column) const override {
        return this->get_column_value_with_core_solver(column, m_core_solver);
    }

    T get_current_cost() const override;
};
}
