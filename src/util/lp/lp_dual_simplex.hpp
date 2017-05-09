/*
  Copyright (c) 2017 Microsoft Corporation
  Author: Lev Nachmanson
*/
#include "util/lp/lp_dual_simplex.h"
namespace lean{

template <typename T, typename X> void lp_dual_simplex<T, X>::decide_on_status_after_stage1() {
    switch (m_core_solver->get_status()) {
    case OPTIMAL:
        if (this->m_settings.abs_val_is_smaller_than_artificial_tolerance(m_core_solver->get_cost())) {
            this->m_status = FEASIBLE;
        } else {
            this->m_status = UNBOUNDED;
        }
        break;
    case DUAL_UNBOUNDED:
        lean_unreachable();
    case ITERATIONS_EXHAUSTED:
        this->m_status = ITERATIONS_EXHAUSTED;
        break;
    case TIME_EXHAUSTED:
        this->m_status = TIME_EXHAUSTED;
        break;
    case FLOATING_POINT_ERROR:
        this->m_status = FLOATING_POINT_ERROR;
        break;
    default:
        lean_unreachable();
    }
}

template <typename T, typename X> void lp_dual_simplex<T, X>::fix_logical_for_stage2(unsigned j) {
    lean_assert(j >= this->number_of_core_structurals());
    switch (m_column_types_of_logicals[j - this->number_of_core_structurals()]) {
    case column_type::low_bound:
        m_low_bounds[j] = numeric_traits<T>::zero();
        m_column_types_of_core_solver[j] = column_type::low_bound;
        m_can_enter_basis[j] = true;
        break;
    case column_type::fixed:
        this->m_upper_bounds[j] = m_low_bounds[j] = numeric_traits<T>::zero();
        m_column_types_of_core_solver[j] = column_type::fixed;
        m_can_enter_basis[j] = false;
        break;
    default:
        lean_unreachable();
    }
}

template <typename T, typename X> void lp_dual_simplex<T, X>::fix_structural_for_stage2(unsigned j) {
    column_info<T> * ci = this->m_map_from_var_index_to_column_info[this->m_core_solver_columns_to_external_columns[j]];
    switch (ci->get_column_type()) {
    case column_type::low_bound:
        m_low_bounds[j] = numeric_traits<T>::zero();
        m_column_types_of_core_solver[j] = column_type::low_bound;
        m_can_enter_basis[j] = true;
        break;
    case column_type::fixed:
    case column_type::upper_bound:
        lean_unreachable();
    case column_type::boxed:
        this->m_upper_bounds[j] = ci->get_adjusted_upper_bound() / this->m_column_scale[j];
        m_low_bounds[j] = numeric_traits<T>::zero();
        m_column_types_of_core_solver[j] = column_type::boxed;
        m_can_enter_basis[j] = true;
        break;
    case column_type::free_column:
        m_can_enter_basis[j] = true;
        m_column_types_of_core_solver[j] = column_type::free_column;
        break;
    default:
        lean_unreachable();
    }
    //    T cost_was = this->m_costs[j];
    this->set_scaled_cost(j);
}

template <typename T, typename X> void lp_dual_simplex<T, X>::unmark_boxed_and_fixed_columns_and_fix_structural_costs() {
    unsigned j = this->m_A->column_count();
    while (j-- > this->number_of_core_structurals()) {
        fix_logical_for_stage2(j);
    }
    j = this->number_of_core_structurals();
    while (j--) {
        fix_structural_for_stage2(j);
    }
}

template <typename T, typename X> void lp_dual_simplex<T, X>::restore_right_sides() {
    unsigned i = this->m_A->row_count();
    while (i--) {
        this->m_b[i] = m_b_copy[i];
    }
}

template <typename T, typename X> void lp_dual_simplex<T, X>::solve_for_stage2() {
    m_core_solver->restore_non_basis();
    m_core_solver->solve_yB(m_core_solver->m_y);
    m_core_solver->fill_reduced_costs_from_m_y_by_rows();
    m_core_solver->start_with_initial_basis_and_make_it_dual_feasible();
    m_core_solver->set_status(FEASIBLE);
    m_core_solver->solve();
    switch (m_core_solver->get_status()) {
    case OPTIMAL:
        this->m_status = OPTIMAL;
        break;
    case DUAL_UNBOUNDED:
        this->m_status = INFEASIBLE;
        break;
    case TIME_EXHAUSTED:
        this->m_status = TIME_EXHAUSTED;
        break;
    case FLOATING_POINT_ERROR:
        this->m_status = FLOATING_POINT_ERROR;
        break;
    default:
        lean_unreachable();
    }
    this->m_second_stage_iterations = m_core_solver->total_iterations();
    this->m_total_iterations = (this->m_first_stage_iterations + this->m_second_stage_iterations);
}

template <typename T, typename X> void lp_dual_simplex<T, X>::fill_x_with_zeros() {
    unsigned j = this->m_A->column_count();
    while (j--) {
        this->m_x[j] = numeric_traits<T>::zero();
    }
}

template <typename T, typename X> void lp_dual_simplex<T, X>::stage1() {
    lean_assert(m_core_solver == nullptr);
    this->m_x.resize(this->m_A->column_count(), numeric_traits<T>::zero());
    if (this->m_settings.get_message_ostream() != nullptr)
        this->print_statistics_on_A(*this->m_settings.get_message_ostream());
    m_core_solver = new lp_dual_core_solver<T, X>(
                                                  *this->m_A,
                                                  m_can_enter_basis,
                                                  this->m_b, // the right side vector
                                                  this->m_x,
                                                  this->m_basis,
                                                  this->m_nbasis,
                                                  this->m_heading,
                                                  this->m_costs,
                                                  this->m_column_types_of_core_solver,
                                                  this->m_low_bounds,
                                                  this->m_upper_bounds,
                                                  this->m_settings,
                                                  *this);
    m_core_solver->fill_reduced_costs_from_m_y_by_rows();
    m_core_solver->start_with_initial_basis_and_make_it_dual_feasible();
    if (this->m_settings.abs_val_is_smaller_than_artificial_tolerance(m_core_solver->get_cost())) {
        // skipping stage 1
        m_core_solver->set_status(OPTIMAL);
        m_core_solver->set_total_iterations(0);
    } else {
        m_core_solver->solve();
    }
    decide_on_status_after_stage1();
    this->m_first_stage_iterations = m_core_solver->total_iterations();
}

template <typename T, typename X> void lp_dual_simplex<T, X>::stage2() {
    unmark_boxed_and_fixed_columns_and_fix_structural_costs();
    restore_right_sides();
    solve_for_stage2();
}

template <typename T, typename X> void lp_dual_simplex<T, X>::fill_first_stage_solver_fields() {
    unsigned slack_var = this->number_of_core_structurals();
    unsigned artificial = this->number_of_core_structurals() + this->m_slacks;

    for (unsigned row = 0; row < this->row_count(); row++) {
        fill_first_stage_solver_fields_for_row_slack_and_artificial(row, slack_var, artificial);
    }
    fill_costs_and_bounds_and_column_types_for_the_first_stage_solver();
}

template <typename T, typename X> column_type lp_dual_simplex<T, X>::get_column_type(unsigned j) {
    lean_assert(j < this->m_A->column_count());
    if (j >= this->number_of_core_structurals()) {
        return m_column_types_of_logicals[j - this->number_of_core_structurals()];
    }
    return this->m_map_from_var_index_to_column_info[this->m_core_solver_columns_to_external_columns[j]]->get_column_type();
}

template <typename T, typename X> void lp_dual_simplex<T, X>::fill_costs_bounds_types_and_can_enter_basis_for_the_first_stage_solver_structural_column(unsigned j) {
    // see 4.7 in the dissertation of Achim Koberstein
    lean_assert(this->m_core_solver_columns_to_external_columns.find(j) !=
                this->m_core_solver_columns_to_external_columns.end());

    T free_bound = T(1e4); // see 4.8
    unsigned jj = this->m_core_solver_columns_to_external_columns[j];
    lean_assert(this->m_map_from_var_index_to_column_info.find(jj) != this->m_map_from_var_index_to_column_info.end());
    column_info<T> * ci = this->m_map_from_var_index_to_column_info[jj];
    switch (ci->get_column_type()) {
    case column_type::upper_bound: {
        std::stringstream s;
        s << "unexpected bound type " << j << " "
          << column_type_to_string(get_column_type(j));
        throw_exception(s.str());
        break;
    }
    case column_type::low_bound: {
        m_can_enter_basis[j] = true;
        this->set_scaled_cost(j);
        this->m_low_bounds[j] = numeric_traits<T>::zero();
        this->m_upper_bounds[j] =numeric_traits<T>::one();
        break;
    }
    case column_type::free_column: {
        m_can_enter_basis[j] = true;
        this->set_scaled_cost(j);
        this->m_upper_bounds[j] = free_bound;
        this->m_low_bounds[j] =  -free_bound;
        break;
    }
    case column_type::boxed:
        m_can_enter_basis[j] = false;
        this->m_costs[j] = numeric_traits<T>::zero();
        this->m_upper_bounds[j] = this->m_low_bounds[j] =  numeric_traits<T>::zero(); // is it needed?
        break;
    default:
        lean_unreachable();
    }
    m_column_types_of_core_solver[j] = column_type::boxed;
}

template <typename T, typename X> void lp_dual_simplex<T, X>::fill_costs_bounds_types_and_can_enter_basis_for_the_first_stage_solver_logical_column(unsigned j) {
    this->m_costs[j] = 0;
    lean_assert(get_column_type(j) != column_type::upper_bound);
    if ((m_can_enter_basis[j] = (get_column_type(j) == column_type::low_bound))) {
        m_column_types_of_core_solver[j] = column_type::boxed;
        this->m_low_bounds[j] = numeric_traits<T>::zero();
        this->m_upper_bounds[j] = numeric_traits<T>::one();
    } else {
        m_column_types_of_core_solver[j] = column_type::fixed;
        this->m_low_bounds[j] = numeric_traits<T>::zero();
        this->m_upper_bounds[j] = numeric_traits<T>::zero();
    }
}

template <typename T, typename X> void lp_dual_simplex<T, X>::fill_costs_and_bounds_and_column_types_for_the_first_stage_solver() {
    unsigned j = this->m_A->column_count();
    while (j-- > this->number_of_core_structurals()) { // go over logicals here
        fill_costs_bounds_types_and_can_enter_basis_for_the_first_stage_solver_logical_column(j);
    }
    j = this->number_of_core_structurals();
    while (j--) {
        fill_costs_bounds_types_and_can_enter_basis_for_the_first_stage_solver_structural_column(j);
    }
}

template <typename T, typename X> void lp_dual_simplex<T, X>::fill_first_stage_solver_fields_for_row_slack_and_artificial(unsigned row,
                                                                                                                          unsigned & slack_var,
                                                                                                                          unsigned & artificial) {
    lean_assert(row < this->row_count());
    auto & constraint = this->m_constraints[this->m_core_solver_rows_to_external_rows[row]];
    // we need to bring the program to the form Ax = b
    T rs = this->m_b[row];
    switch (constraint.m_relation) {
    case Equal: // no slack variable here
        set_type_for_logical(artificial, column_type::fixed);
        this->m_basis[row] = artificial;
        this->m_costs[artificial] = numeric_traits<T>::zero();
        (*this->m_A)(row, artificial) = numeric_traits<T>::one();
        artificial++;
        break;

    case Greater_or_equal:
        set_type_for_logical(slack_var, column_type::low_bound);
        (*this->m_A)(row, slack_var) = - numeric_traits<T>::one();
        if (rs > 0) {
            // adding one artificial
            set_type_for_logical(artificial, column_type::fixed);
            (*this->m_A)(row, artificial) = numeric_traits<T>::one();
            this->m_basis[row] = artificial;
            this->m_costs[artificial] = numeric_traits<T>::zero();
            artificial++;
        } else {
            // we can put a slack_var into the basis, and avoid adding an artificial variable
            this->m_basis[row] = slack_var;
            this->m_costs[slack_var] = numeric_traits<T>::zero();
        }
        slack_var++;
        break;
    case Less_or_equal:
        // introduce a non-negative slack variable
        set_type_for_logical(slack_var, column_type::low_bound);
        (*this->m_A)(row, slack_var) = numeric_traits<T>::one();
        if (rs < 0) {
            // adding one artificial
            set_type_for_logical(artificial, column_type::fixed);
            (*this->m_A)(row, artificial) = - numeric_traits<T>::one();
            this->m_basis[row] = artificial;
            this->m_costs[artificial] = numeric_traits<T>::zero();
            artificial++;
        } else {
            // we can put slack_var into the basis, and avoid adding an artificial variable
            this->m_basis[row] = slack_var;
            this->m_costs[slack_var] = numeric_traits<T>::zero();
        }
        slack_var++;
        break;
    }
}

template <typename T, typename X> void lp_dual_simplex<T, X>::augment_matrix_A_and_fill_x_and_allocate_some_fields() {
    this->count_slacks_and_artificials();
    this->m_A->add_columns_at_the_end(this->m_slacks + this->m_artificials);
    unsigned n = this->m_A->column_count();
    this->m_column_types_of_core_solver.resize(n);
    m_column_types_of_logicals.resize(this->m_slacks + this->m_artificials);
    this->m_costs.resize(n);
    this->m_upper_bounds.resize(n);
    this->m_low_bounds.resize(n);
    m_can_enter_basis.resize(n);
    this->m_basis.resize(this->m_A->row_count());
}



template <typename T, typename X> void lp_dual_simplex<T, X>::copy_m_b_aside_and_set_it_to_zeros() {
    for (unsigned i = 0; i < this->m_b.size(); i++) {
        m_b_copy.push_back(this->m_b[i]);
        this->m_b[i] = numeric_traits<T>::zero(); // preparing for the first stage
    }
}

template <typename T, typename X> void lp_dual_simplex<T, X>::find_maximal_solution(){
    if (this->problem_is_empty()) {
        this->m_status = lp_status::EMPTY;
        return;
    }

    this->flip_costs(); // do it for now, todo ( remove the flipping)

    this->cleanup();
    if (this->m_status == INFEASIBLE) {
        return;
    }
    this->fill_matrix_A_and_init_right_side();
    this->fill_m_b();
    this->scale();
    augment_matrix_A_and_fill_x_and_allocate_some_fields();
    fill_first_stage_solver_fields();
    copy_m_b_aside_and_set_it_to_zeros();
    stage1();
    if (this->m_status == FEASIBLE) {
        stage2();
    }
}


template <typename T, typename X> T lp_dual_simplex<T, X>::get_current_cost() const {
    T ret = numeric_traits<T>::zero();
    for (auto it : this->m_map_from_var_index_to_column_info) {
        ret += this->get_column_cost_value(it.first, it.second);
    }
    return -ret; // we flip costs for now
}
}
