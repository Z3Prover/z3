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

#include <set>
#include <string>
#include "util/vector.h"
#include "math/lp/lp_utils.h"
#include "math/lp/lp_core_solver_base.h"
namespace lp {

template <typename T, typename X> lp_core_solver_base<T, X>::
lp_core_solver_base(static_matrix<T, X> & A,
                    // vector<X> & b, // the right side vector
                    vector<unsigned> & basis,
                    vector<unsigned> & nbasis,
                    vector<int> & heading,
                    vector<X> & x,
                    vector<T> & costs,
                    lp_settings & settings,
                    const column_namer& column_names,
                    const vector<column_type> & column_types,
                    const vector<X> & lower_bound_values,
                    const vector<X> & upper_bound_values):
    m_total_iterations(0),
    m_iters_with_no_cost_growing(0),
    m_status(lp_status::FEASIBLE),
    m_inf_set(A.column_count()),
    m_pivot_row(A.column_count()),
    m_A(A),
    m_basis(basis),
    m_nbasis(nbasis),
    m_basis_heading(heading),
    m_x(x),
    m_costs(costs),
    m_settings(settings),
    m_column_names(column_names),
    m_d(m_n()),
    m_column_types(column_types),
    m_lower_bounds(lower_bound_values),
    m_upper_bounds(upper_bound_values),
    m_basis_sort_counter(0),
    m_tracing_basis_changes(false),
    m_pivoted_rows(nullptr),
    m_look_for_feasible_solution_only(false) {
    lp_assert(bounds_for_boxed_are_set_correctly());    
    init();
    init_basis_heading_and_non_basic_columns_vector();
}

template <typename T, typename X> void lp_core_solver_base<T, X>::
allocate_basis_heading() { // the rest of initialization will be handled by the factorization class
    init_basis_heading_and_non_basic_columns_vector();
    lp_assert(basis_heading_is_correct());
}
template <typename T, typename X> void lp_core_solver_base<T, X>::
init() {    
    allocate_basis_heading();
    
}

// i is the pivot row, and j is the pivot column
template <typename T, typename X> void lp_core_solver_base<T, X>::
pivot_to_reduced_costs_tableau(unsigned i, unsigned j) {
    if (j >= m_d.size())
        return;
    T &a = m_d[j];
    if (is_zero(a))
        return;
    for (const row_cell<T> & r: m_A.m_rows[i]){
        if (r.var() != j)
            m_d[r.var()] -= a * r.coeff();
    }
    a = zero_of_type<T>(); // zero the pivot column's m_d finally
}



// template <typename T, typename X> void lp_core_solver_base<T, X>::
// update_index_of_ed() {
//     m_index_of_ed.clear();
//     unsigned i = static_cast<unsigned>(m_ed.size());
//     while (i--) {
//         if (!is_zero(m_ed[i]))
//             m_index_of_ed.push_back(i);
//     }
// }




template <typename T, typename X> void lp_core_solver_base<T, X>::
pretty_print(std::ostream & out) {
    core_solver_pretty_printer<T, X> pp(*this, out);
    pp.print();
}


template <typename T, typename X> void lp_core_solver_base<T, X>::
add_delta_to_entering(unsigned entering, const X& delta) {
    m_x[entering] += delta;
     
        for (const auto & c : m_A.m_columns[entering]) {
            unsigned i = c.var();
            m_x[m_basis[i]] -= delta * m_A.get_val(c);
        }
}


template <typename T, typename X> void lp_core_solver_base<T, X>::
print_statistics(char const* str, X cost, std::ostream & out) {
    if (str!= nullptr)
        out << str << " ";
    out << "iterations = " << (total_iterations() - 1) << ", cost = " << T_to_string(cost)
        << ", nonzeros = " <<  m_A.number_of_non_zeroes() << std::endl;
}

template <typename T, typename X> bool lp_core_solver_base<T, X>::
print_statistics_with_iterations_and_check_that_the_time_is_over(std::ostream & str) {
    unsigned total_iterations = inc_total_iterations();
    if (m_settings.report_frequency != 0)  {
        if (m_settings.print_statistics && (total_iterations % m_settings.report_frequency == 0)) {
            print_statistics("", X(), str);
        }
    }
    return time_is_over();
}

template <typename T, typename X> bool lp_core_solver_base<T, X>::
print_statistics_with_iterations_and_nonzeroes_and_cost_and_check_that_the_time_is_over(char const* str, std::ostream & out) {
    unsigned total_iterations = inc_total_iterations();
    if (m_settings.report_frequency != 0)
        if (m_settings.print_statistics && (total_iterations % m_settings.report_frequency == 0)) {
            print_statistics(str, get_cost(), out);
        }
    return time_is_over();
}

template <typename T, typename X> bool lp_core_solver_base<T, X>::
print_statistics_with_cost_and_check_that_the_time_is_over(X cost, std::ostream & out) {
    unsigned total_iterations = inc_total_iterations();
    if (m_settings.report_frequency != 0)
        if (m_settings.print_statistics && (total_iterations % m_settings.report_frequency == 0)) {
            print_statistics("", cost, out);
        }
    return time_is_over();
}

template <typename T, typename X> bool lp_core_solver_base<T, X>::
column_is_dual_feasible(unsigned j) const {
    switch (m_column_types[j]) {
    case column_type::fixed:
    case column_type::boxed:
        return (x_is_at_lower_bound(j) && d_is_not_negative(j)) ||
            (x_is_at_upper_bound(j) && d_is_not_positive(j));
    case column_type::lower_bound:
        return x_is_at_lower_bound(j) && d_is_not_negative(j);
    case column_type::upper_bound:
        UNREACHABLE();
        break;
    case column_type::free_column:
        return numeric_traits<X>::is_zero(m_d[j]);
    default:
        UNREACHABLE();
    }
    UNREACHABLE();
    return false;
}
template <typename T, typename X> bool lp_core_solver_base<T, X>::
d_is_not_negative(unsigned j) const {
    return m_d[j] >= numeric_traits<T>::zero();
}

template <typename T, typename X> bool lp_core_solver_base<T, X>::
d_is_not_positive(unsigned j) const {
    return m_d[j] <= numeric_traits<T>::zero();    
}


template <typename T, typename X> bool lp_core_solver_base<T, X>::
time_is_over() {
    if (m_settings.get_cancel_flag()) {
        m_status = lp_status::TIME_EXHAUSTED;
        return true;
    }
    else {
        return false;
    }
}

template <typename T, typename X> void lp_core_solver_base<T, X>::
rs_minus_Anx(vector<X> & rs) {
    unsigned row = m_m();
    while (row--) {
        auto& rsv = rs[row] = zero_of_type<X>(); //m_b[row];
        for (auto & it : m_A.m_rows[row]) {
            unsigned j = it.var();
            if (m_basis_heading[j] < 0) {
                rsv -= m_x[j] * it.coeff();
            }
        }
    }
}

template <typename T, typename X> bool lp_core_solver_base<T, X>::column_is_feasible(unsigned j) const {
    const X& x = this->m_x[j];
    switch (this->m_column_types[j]) {
    case column_type::fixed:
    case column_type::boxed:
        return !this->above_bound(x, this->m_upper_bounds[j]) && 
               !this->below_bound(x, this->m_lower_bounds[j]);
    case column_type::lower_bound:
        return !this->below_bound(x, this->m_lower_bounds[j]);
    case column_type::upper_bound:
        return !this->above_bound(x, this->m_upper_bounds[j]);
    case column_type::free_column:
        return true;
        break;
    default:
        UNREACHABLE();
    }
    return false; // it is unreachable
}

template <typename T, typename X> bool lp_core_solver_base<T, X>::calc_current_x_is_feasible_include_non_basis() const {
    unsigned j = this->m_n();
    while (j--) {
        if (!column_is_feasible(j)) {
            TRACE("lar_solver", tout << "infeasible column: "; print_column_info(j, tout) << "\n";);
            return false;
        }
    }
    return true;
}

template <typename T, typename X> bool lp_core_solver_base<T, X>::inf_set_is_correct() const {
    for (unsigned j = 0; j < this->m_n(); j++) {
        bool belongs_to_set = m_inf_set.contains(j);
        bool is_feas = column_is_feasible(j);
        if (is_feas == belongs_to_set) {
            TRACE("lp_core", tout << "incorrectly set column in inf set "; print_column_info(j, tout) << "\n";);
            return false;
        }
    }
    return true;
}


template <typename T, typename X> bool lp_core_solver_base<T, X>::
divide_row_by_pivot(unsigned pivot_row, unsigned pivot_col) {
    int pivot_index = -1;
    auto & row = m_A.m_rows[pivot_row];
    unsigned size = row.size();
    for (unsigned j = 0; j < size; j++) {
        auto & c = row[j];
        if (c.var() == pivot_col) {
            pivot_index = static_cast<int>(j);
            break;
        }
    }
    if (pivot_index == -1)
        return false;
    auto & pivot_cell = row[pivot_index];
    T & coeff = pivot_cell.coeff();
    if (is_zero(coeff)) 
        return false;
    
    // this->m_b[pivot_row] /= coeff;
    for (unsigned j = 0; j < size; j++) {
        auto & c = row[j];
        if (c.var() != pivot_col) {
            c.coeff() /= coeff;
        }
    }
    coeff = one_of_type<T>();
    CASSERT("check_static_matrix", m_A.is_correct());
    return true;
}
template <typename T, typename X> bool lp_core_solver_base<T, X>::
pivot_column_tableau(unsigned j, unsigned piv_row_index) {
	if (!divide_row_by_pivot(piv_row_index, j))
        return false;
    auto &column = m_A.m_columns[j];
    int pivot_col_cell_index = -1;
    for (unsigned k = 0; k < column.size(); k++) {
        if (column[k].var() == piv_row_index) {
            pivot_col_cell_index = k;
            break;
        }
    }
    if (pivot_col_cell_index < 0)
        return false;
        
    if (pivot_col_cell_index != 0) {
        lp_assert(column.size() > 1);
        // swap the pivot column cell with the head cell
        auto c = column[0];
        column[0]  = column[pivot_col_cell_index];
        column[pivot_col_cell_index] = c;

        m_A.m_rows[piv_row_index][column[0].offset()].offset() = 0;
        m_A.m_rows[c.var()][c.offset()].offset() = pivot_col_cell_index;
    }
    while (column.size() > 1) {
        auto & c = column.back();
        lp_assert(c.var() != piv_row_index);
        if(! m_A.pivot_row_to_row_given_cell(piv_row_index, c, j)) {
            return false;
        }
        if (m_pivoted_rows!= nullptr)
            m_pivoted_rows->insert(c.var());
    }

    if (m_settings.simplex_strategy() == simplex_strategy_enum::tableau_costs)
        pivot_to_reduced_costs_tableau(piv_row_index, j);
    return true;
}


template <typename T, typename X> bool lp_core_solver_base<T, X>::
basis_has_no_doubles() const {
    std::set<unsigned> bm;
    for (unsigned i = 0; i < m_m(); i++) {
        bm.insert(m_basis[i]);
    }
    return bm.size() == m_m();
}

template <typename T, typename X> bool lp_core_solver_base<T, X>::
non_basis_has_no_doubles() const {
    std::set<int> bm;
    for (auto j : m_nbasis) 
        bm.insert(j);    
    return bm.size() == m_nbasis.size();
}

template <typename T, typename X> bool lp_core_solver_base<T, X>::
basis_is_correctly_represented_in_heading() const {
    for (unsigned i = 0; i < m_m(); i++) 
        if (m_basis_heading[m_basis[i]] != static_cast<int>(i))
            return false;    
    return true;
}
template <typename T, typename X> bool lp_core_solver_base<T, X>::
non_basis_is_correctly_represented_in_heading() const {
    for (unsigned i = 0; i < m_nbasis.size(); i++) 
        if (m_basis_heading[m_nbasis[i]] !=  - static_cast<int>(i) - 1)
            return false;
    
    for (unsigned j = 0; j < m_A.column_count(); j++) 
        if (m_basis_heading[j] >= 0)
            lp_assert(static_cast<unsigned>(m_basis_heading[j]) < m_A.row_count() && m_basis[m_basis_heading[j]] == j);
        
    return true;
}

template <typename T, typename X> bool lp_core_solver_base<T, X>::
    basis_heading_is_correct() const {
    if ( m_A.column_count() > 10 )  // for the performance reason
        return true;
    
    lp_assert(m_basis_heading.size() == m_A.column_count());
    lp_assert(m_basis.size() == m_A.row_count());
    lp_assert(m_nbasis.size() <= m_A.column_count() - m_A.row_count()); // for the dual the size of non basis can be smaller

    if (!basis_has_no_doubles()) 
        return false;
    
    if (!non_basis_has_no_doubles()) 
        return false;
    
    if (!basis_is_correctly_represented_in_heading()) 
        return false;    

    if (!non_basis_is_correctly_represented_in_heading()) 
        return false;
    
    return true;
}

template <typename T, typename X> std::string lp_core_solver_base<T, X>::
column_name(unsigned column) const {
    return m_column_names.get_variable_name(column);
}

template <typename T, typename X>  void lp_core_solver_base<T, X>::transpose_rows_tableau(unsigned i, unsigned j) {
    transpose_basis(i, j);
    m_A.transpose_rows(i, j);
}
// j is the new basic column, j_basic - the leaving column
template <typename T, typename X> bool lp_core_solver_base<T, X>::pivot_column_general(unsigned j, unsigned j_basic, indexed_vector<T> & w) {
	lp_assert(m_basis_heading[j] < 0);
	lp_assert(m_basis_heading[j_basic] >= 0);
	unsigned row_index = m_basis_heading[j_basic];
	  // the tableau case
	if (pivot_column_tableau(j, row_index))
		change_basis(j, j_basic);
	else return false;
	
	return true;
}


template <typename T, typename X> bool lp_core_solver_base<T, X>::remove_from_basis(unsigned basic_j) {
    indexed_vector<T> w(m_basis.size()); // the buffer
    unsigned i = m_basis_heading[basic_j];
    for (auto &c : m_A.m_rows[i]) {
        if (c.var() == basic_j)
            continue;
        if (pivot_column_general(c.var(), basic_j, w))
            return true;
    }
    return false;
}


}
