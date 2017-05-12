/*
  Copyright (c) 2017 Microsoft Corporation
  Author: Lev Nachmanson
*/
#include <set>
#include <string>
#include "util/vector.h"
#include "util/lp/lp_utils.h"
#include "util/lp/lp_core_solver_base.h"
namespace lean {

template <typename T, typename X> lp_core_solver_base<T, X>::
lp_core_solver_base(static_matrix<T, X> & A,
                    vector<X> & b, // the right side vector
                    vector<unsigned> & basis,
                    vector<unsigned> & nbasis,
                    vector<int> & heading,
                    vector<X> & x,
                    vector<T> & costs,
                    lp_settings & settings,
                    const column_namer& column_names,
                    const vector<column_type> & column_types,
                    const vector<X> & low_bound_values,
                    const vector<X> & upper_bound_values):
    m_total_iterations(0),
    m_iters_with_no_cost_growing(0),
    m_status(FEASIBLE),
    m_inf_set(A.column_count()),
    m_using_infeas_costs(false),
    m_pivot_row_of_B_1(A.row_count()),
    m_pivot_row(A.column_count()),
    m_A(A),
    m_b(b),
    m_basis(basis),
    m_nbasis(nbasis),
    m_basis_heading(heading),
    m_x(x),
    m_costs(costs),
    m_settings(settings),
    m_y(m_m()),
    m_factorization(nullptr),
    m_column_names(column_names),
    m_w(m_m()),
    m_d(m_n()),
    m_ed(m_m()),
    m_column_types(column_types),
    m_low_bounds(low_bound_values),
    m_upper_bounds(upper_bound_values),
    m_column_norms(m_n()),
    m_copy_of_xB(m_m()),
    m_basis_sort_counter(0),
    m_steepest_edge_coefficients(A.column_count()),
    m_tracing_basis_changes(false),
    m_pivoted_rows(nullptr),
    m_look_for_feasible_solution_only(false) {
    lean_assert(bounds_for_boxed_are_set_correctly());    
    init();
    init_basis_heading_and_non_basic_columns_vector();
}

template <typename T, typename X> void lp_core_solver_base<T, X>::
allocate_basis_heading() { // the rest of initilization will be handled by the factorization class
    init_basis_heading_and_non_basic_columns_vector();
    lean_assert(basis_heading_is_correct());
}
template <typename T, typename X> void lp_core_solver_base<T, X>::
init() {    
    allocate_basis_heading();
    if (m_settings.use_lu())
        init_factorization(m_factorization, m_A, m_basis, m_settings);
}

template <typename T, typename X> bool lp_core_solver_base<T, X>::
pivot_for_tableau_on_basis() {
    m_d = m_costs; // we will be pivoting to m_d as well
    unsigned m = m_A.row_count();
    for (unsigned i = 0; i < m; i++)
        if (!pivot_column_tableau(m_basis[i], i))
            return false;
    return true;
}

// i is the pivot row, and j is the pivot column
template <typename T, typename X> void lp_core_solver_base<T, X>::
pivot_to_reduced_costs_tableau(unsigned i, unsigned j) {
	if (j >= m_d.size())
		return;
    T &a = m_d[j];
    if (is_zero(a))
        return;
    for (const row_cell<T> & r: m_A.m_rows[i])
        if (r.m_j != j)
            m_d[r.m_j] -= a * r.get_val();

    a = zero_of_type<T>(); // zero the pivot column's m_d finally
}


template <typename T, typename X> void lp_core_solver_base<T, X>::
fill_cb(T * y){
    for (unsigned i = 0; i < m_m(); i++) {
        y[i] = m_costs[m_basis[i]];
    }
}


template <typename T, typename X> void lp_core_solver_base<T, X>::
fill_cb(vector<T> & y){
    for (unsigned i = 0; i < m_m(); i++) {
        y[i] = m_costs[m_basis[i]];
    }
}

template <typename T, typename X> void lp_core_solver_base<T, X>::
solve_yB(vector<T> & y) {
    fill_cb(y); // now y = cB, that is the projection of costs to basis
    m_factorization->solve_yB_with_error_check(y, m_basis);
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
template <typename T, typename X> void lp_core_solver_base<T, X>::solve_Bd(unsigned entering, indexed_vector<T> & column) {
    lean_assert(!m_settings.use_tableau());
    if (m_factorization == nullptr) {
        init_factorization(m_factorization, m_A, m_basis, m_settings);
    }
    m_factorization->solve_Bd_faster(entering, column);
}


template <typename T, typename X> void lp_core_solver_base<T, X>::
solve_Bd(unsigned entering) {
    lean_assert(m_ed.is_OK());
    m_factorization->solve_Bd(entering, m_ed, m_w);
    if (this->precise())
        m_columns_nz[entering] = m_ed.m_index.size();
    lean_assert(m_ed.is_OK());
    lean_assert(m_w.is_OK());
#ifdef LEAN_DEBUG
    // auto B = get_B(*m_factorization, m_basis);
    // vector<T>  a(m_m());
    // m_A.copy_column_to_vector(entering, a);
    // vector<T> cd(m_ed.m_data);
    // B.apply_from_left(cd, m_settings);
    // lean_assert(vectors_are_equal(cd , a));
#endif
}

template <typename T, typename X> void lp_core_solver_base<T, X>::
pretty_print(std::ostream & out) {
    core_solver_pretty_printer<T, X> pp(*this, out);
    pp.print();
}

template <typename T, typename X> void lp_core_solver_base<T, X>::
save_state(T * w_buffer, T * d_buffer) {
    copy_m_w(w_buffer);
    copy_m_ed(d_buffer);
}

template <typename T, typename X> void lp_core_solver_base<T, X>::
restore_state(T * w_buffer, T * d_buffer) {
    restore_m_w(w_buffer);
    restore_m_ed(d_buffer);
}

template <typename T, typename X> void lp_core_solver_base<T, X>::
copy_m_w(T * buffer) {
    unsigned i = m_m();
    while (i --) {
        buffer[i] = m_w[i];
    }
}

template <typename T, typename X> void lp_core_solver_base<T, X>::
restore_m_w(T * buffer) {
    m_w.m_index.clear();
    unsigned i = m_m();
    while (i--) {
        if (!is_zero(m_w[i] = buffer[i]))
            m_w.m_index.push_back(i);
    }
}

// needed for debugging
template <typename T, typename X> void lp_core_solver_base<T, X>::
copy_m_ed(T * buffer) {
    unsigned i = m_m();
    while (i --) {
        buffer[i] = m_ed[i];
    }
}

template <typename T, typename X> void lp_core_solver_base<T, X>::
restore_m_ed(T * buffer) {
    unsigned i = m_m();
    while (i --) {
        m_ed[i] = buffer[i];
    }
}

template <typename T, typename X> bool lp_core_solver_base<T, X>::
A_mult_x_is_off() const {
    lean_assert(m_x.size() == m_A.column_count());
    if (numeric_traits<T>::precise()) {
        for (unsigned i = 0; i < m_m(); i++) {
            X delta = m_b[i] - m_A.dot_product_with_row(i, m_x);
            if (delta != numeric_traits<X>::zero()) {
                std::cout << "precise x is off (";
                std::cout << "m_b[" << i << "] = " << m_b[i] << " ";
                std::cout << "left side = " << m_A.dot_product_with_row(i, m_x) << ' ';
                std::cout << "delta = " << delta << ' ';
                std::cout << "iters = " << total_iterations() << ")" << std::endl;
                return true;
            }
        }
        return false;
    }
    T feps = convert_struct<T, double>::convert(m_settings.refactor_tolerance);
    X one = convert_struct<X, double>::convert(1.0);
    for (unsigned i = 0; i < m_m(); i++) {
        X delta = abs(m_b[i] - m_A.dot_product_with_row(i, m_x));
        X eps = feps * (one + T(0.1) * abs(m_b[i]));

        if (delta > eps) {
#if 0
            LP_OUT(m_settings, "x is off ("
                << "m_b[" << i  << "] = " << m_b[i] << " "
                << "left side = " << m_A.dot_product_with_row(i, m_x) << ' '
                << "delta = " << delta << ' '
                   << "iters = " << total_iterations() << ")" << std::endl);
#endif
            return true;
        }
    }
    return false;
}
template <typename T, typename X> bool lp_core_solver_base<T, X>::
A_mult_x_is_off_on_index(const vector<unsigned> & index) const {
    lean_assert(m_x.size() == m_A.column_count());
    if (numeric_traits<T>::precise()) return false;
#if RUN_A_MULT_X_IS_OFF_FOR_PRECESE
    for (unsigned i : index) {
        X delta = m_b[i] - m_A.dot_product_with_row(i, m_x);
        if (delta != numeric_traits<X>::zero()) {
            // std::cout << "x is off (";
            // std::cout << "m_b[" << i  << "] = " << m_b[i] << " ";
            // std::cout << "left side = " << m_A.dot_product_with_row(i, m_x) << ' ';
            // std::cout << "delta = " << delta << ' ';
            // std::cout << "iters = " << total_iterations() << ")" << std::endl;
            return true;
        }
    }
    return false;
#endif
    // todo(levnach) run on m_ed.m_index only !!!!!
    T feps = convert_struct<T, double>::convert(m_settings.refactor_tolerance);
    X one = convert_struct<X, double>::convert(1.0);
    for (unsigned i : index) {
        X delta = abs(m_b[i] - m_A.dot_product_with_row(i, m_x));
        X eps = feps * (one + T(0.1) * abs(m_b[i]));

        if (delta > eps) {
#if 0
            LP_OUT(m_settings, "x is off ("
                << "m_b[" << i  << "] = " << m_b[i] << " "
                << "left side = " << m_A.dot_product_with_row(i, m_x) << ' '
                << "delta = " << delta << ' '
                   << "iters = " << total_iterations() << ")" << std::endl);
#endif
            return true;
        }
    }
    return false;
}

// from page 182 of Istvan Maros's book
template <typename T, typename X> void lp_core_solver_base<T, X>::
calculate_pivot_row_of_B_1(unsigned pivot_row) {
    lean_assert(! use_tableau());
    lean_assert(m_pivot_row_of_B_1.is_OK());
    m_pivot_row_of_B_1.clear();
    m_pivot_row_of_B_1.set_value(numeric_traits<T>::one(), pivot_row);
    lean_assert(m_pivot_row_of_B_1.is_OK());
    m_factorization->solve_yB_with_error_check_indexed(m_pivot_row_of_B_1, m_basis_heading, m_basis, m_settings);
    lean_assert(m_pivot_row_of_B_1.is_OK());
}


template <typename T, typename X> void lp_core_solver_base<T, X>::
calculate_pivot_row_when_pivot_row_of_B1_is_ready(unsigned pivot_row) {
    m_pivot_row.clear();

    for (unsigned i : m_pivot_row_of_B_1.m_index) {
        const T & pi_1 = m_pivot_row_of_B_1[i];
        if (numeric_traits<T>::is_zero(pi_1)) {
            continue;
        }
        for (auto & c : m_A.m_rows[i]) {
            unsigned j = c.m_j;
            if (m_basis_heading[j] < 0) {
                m_pivot_row.add_value_at_index_with_drop_tolerance(j, c.get_val() * pi_1);
            }
        }
    }
    if (precise()) {
        m_rows_nz[pivot_row] = m_pivot_row.m_index.size();
    }
}

template <typename T, typename X> void lp_core_solver_base<T, X>::
update_x(unsigned entering, const X& delta) {
    m_x[entering] += delta;
    if (!use_tableau())
        for (unsigned i : m_ed.m_index) {
            if (!numeric_traits<X>::precise()) 
                m_copy_of_xB[i] = m_x[m_basis[i]];
            m_x[m_basis[i]] -= delta * m_ed[i];
        }
    else 
        for (const auto & c : m_A.m_columns[entering]) {
            unsigned i = c.m_i;
            m_x[m_basis[i]] -= delta * m_A.get_val(c);
        }
}


template <typename T, typename X> void lp_core_solver_base<T, X>::
print_statistics(char const* str, X cost, std::ostream & out) {
    if (str!= nullptr)
        out << str << " ";
    out << "iterations = " << (total_iterations() - 1) << ", cost = " << T_to_string(cost)
        << ", nonzeros = " << (m_factorization != nullptr? m_factorization->get_number_of_nonzeroes() : m_A.number_of_non_zeroes()) << std::endl;
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

template <typename T, typename X> void lp_core_solver_base<T, X>::
set_non_basic_x_to_correct_bounds() {
    for (unsigned j : non_basis()) {
        switch (m_column_types[j]) {
        case column_type::boxed:
            m_x[j] = m_d[j] < 0? m_upper_bounds[j]: m_low_bounds[j];
            break;
        case column_type::low_bound:
            m_x[j] = m_low_bounds[j];
            lean_assert(column_is_dual_feasible(j));
            break;
        case column_type::upper_bound:
            m_x[j] = m_upper_bounds[j];
            lean_assert(column_is_dual_feasible(j));
            break;
        default:
            break;
        }
    }
}
template <typename T, typename X> bool lp_core_solver_base<T, X>::
column_is_dual_feasible(unsigned j) const {
    switch (m_column_types[j]) {
    case column_type::fixed:
    case column_type::boxed:
        return (x_is_at_low_bound(j) && d_is_not_negative(j)) ||
            (x_is_at_upper_bound(j) && d_is_not_positive(j));
    case column_type::low_bound:
        return x_is_at_low_bound(j) && d_is_not_negative(j);
    case column_type::upper_bound:
        LP_OUT(m_settings,  "upper_bound type should be switched to low_bound" << std::endl);
        lean_assert(false); // impossible case
    case column_type::free_column:
        return numeric_traits<X>::is_zero(m_d[j]);
    default:
        LP_OUT(m_settings,  "column = " << j << std::endl);
        LP_OUT(m_settings,  "unexpected column type = " << column_type_to_string(m_column_types[j]) << std::endl);
        lean_unreachable();
    }
    lean_unreachable();
    return false;
}
template <typename T, typename X> bool lp_core_solver_base<T, X>::
d_is_not_negative(unsigned j) const {
    if (numeric_traits<T>::precise()) {
        return m_d[j] >= numeric_traits<T>::zero();
    }
    return m_d[j] > -T(0.00001);
}

template <typename T, typename X> bool lp_core_solver_base<T, X>::
d_is_not_positive(unsigned j) const {
    if (numeric_traits<T>::precise()) {
        return m_d[j] <= numeric_traits<T>::zero();
    }
    return m_d[j] < T(0.00001);
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
        auto &rsv = rs[row] = m_b[row];
        for (auto & it : m_A.m_rows[row]) {
            unsigned j = it.m_j;
            if (m_basis_heading[j] < 0) {
                rsv -= m_x[j] * it.get_val();
            }
        }
    }
}

template <typename T, typename X> bool lp_core_solver_base<T, X>::
find_x_by_solving() {
    solve_Ax_eq_b();
    bool ret=  !A_mult_x_is_off();
    return ret;
}

template <typename T, typename X> bool lp_core_solver_base<T, X>::column_is_feasible(unsigned j) const {
    const X& x = this->m_x[j];
    switch (this->m_column_types[j]) {
    case column_type::fixed:
    case column_type::boxed:
        if (this->above_bound(x, this->m_upper_bounds[j])) {
            return false;
        } else if (this->below_bound(x, this->m_low_bounds[j])) {
            return false;
        } else {
            return true;
        }
        break;
    case column_type::low_bound:
        if (this->below_bound(x, this->m_low_bounds[j])) {
            return false;
        } else {
            return true;
        }
        break;
    case column_type::upper_bound:
        if (this->above_bound(x, this->m_upper_bounds[j])) {
            return false;
        } else {
            return true;
        }
        break;
    case column_type::free_column:
        return true;
        break;
    default:
        lean_unreachable();
    }
    return false; // it is unreachable
}

template <typename T, typename X> bool lp_core_solver_base<T, X>::calc_current_x_is_feasible_include_non_basis() const {
    unsigned j = this->m_n();
    while (j--) {
        if (!column_is_feasible(j)) {
            return false;
        }
    }
    return true;
}

template <typename T, typename X> bool lp_core_solver_base<T, X>::inf_set_is_correct() const {
    unsigned j = this->m_n();
    while (j--) {
        bool belongs_to_set = m_inf_set.contains(j);
        bool is_feas = column_is_feasible(j);
    
        if (is_feas == belongs_to_set) {
            print_column_info(j, std::cout);
            std::cout << "belongs_to_set = " << belongs_to_set << std::endl;
            std::cout <<( is_feas? "feas":"inf") << std::endl;
            return false;
        }
    }
    return true;
}

template <typename T, typename X> bool lp_core_solver_base<T, X>::
update_basis_and_x(int entering, int leaving, X const & tt) {
    
    if (!is_zero(tt)) {
        update_x(entering, tt);
        if ((!numeric_traits<T>::precise()) && A_mult_x_is_off_on_index(m_ed.m_index) && !find_x_by_solving()) {
            init_factorization(m_factorization, m_A, m_basis, m_settings);
            if (!find_x_by_solving()) {
                restore_x(entering, tt);
                if(A_mult_x_is_off()) {
                    m_status = FLOATING_POINT_ERROR;
                    m_iters_with_no_cost_growing++;
                    return false;
                }
                    
                init_factorization(m_factorization, m_A, m_basis, m_settings);
                m_iters_with_no_cost_growing++;
                if (m_factorization->get_status() != LU_status::OK) {
                    std::stringstream s;
                    //                    s << "failing refactor on off_result for entering = " << entering << ", leaving = " << leaving << " total_iterations = " << total_iterations();
                    m_status = FLOATING_POINT_ERROR;
                    return false;
                }
                return false;
            }
        }
    }

    bool refactor = m_factorization->need_to_refactor();
    if (!refactor) {
        const T &  pivot = this->m_pivot_row[entering]; // m_ed[m_factorization->basis_heading(leaving)] is the same but the one that we are using is more precise
        m_factorization->replace_column(pivot, m_w, m_basis_heading[leaving]);
        if (m_factorization->get_status() == LU_status::OK) {
            change_basis(entering, leaving);
            return true;
        }
    }
    // need to refactor == true
    change_basis(entering, leaving);
    init_lu();
    if (m_factorization->get_status() != LU_status::OK) {
        if (m_look_for_feasible_solution_only && !precise()) {
            m_status = UNSTABLE;
            delete m_factorization;
            m_factorization = nullptr;
            return false; 
        }
        //        LP_OUT(m_settings, "failing refactor for entering = " << entering << ", leaving = " << leaving << " total_iterations = " << total_iterations() << std::endl);
        restore_x_and_refactor(entering, leaving, tt);
        if (m_status == FLOATING_POINT_ERROR)
            return false;
        lean_assert(!A_mult_x_is_off());
        m_iters_with_no_cost_growing++;
        //        LP_OUT(m_settings, "rolled back after failing of init_factorization()" << std::endl);
        m_status = UNSTABLE;
        return false;
    }
    return true;
}


template <typename T, typename X> bool lp_core_solver_base<T, X>::
divide_row_by_pivot(unsigned pivot_row, unsigned pivot_col) {
    lean_assert(numeric_traits<T>::precise());
    int pivot_index = -1;
    auto & row = m_A.m_rows[pivot_row];
    unsigned size = row.size();
    for (unsigned j = 0; j < size; j++) {
        if (row[j].m_j == pivot_col) {
            pivot_index = static_cast<int>(j);
            break;
        }
    }
    if (pivot_index == -1)
        return false;
    auto & pivot_cell = row[pivot_index];
    if (is_zero(pivot_cell.m_value)) 
        return false;
    
    this->m_b[pivot_row] /= pivot_cell.m_value;
    for (unsigned j = 0; j < size; j++) {
        if (row[j].m_j != pivot_col) {
            row[j].m_value /= pivot_cell.m_value;
        }
    }
    pivot_cell.m_value = one_of_type<T>();
    return true;
}
template <typename T, typename X> bool lp_core_solver_base<T, X>::
pivot_column_tableau(unsigned j, unsigned piv_row_index) {
    if (!divide_row_by_pivot(piv_row_index, j))
        return false;
    auto &column = m_A.m_columns[j];
    int pivot_col_cell_index = -1;
    for (unsigned k = 0; k < column.size(); k++) {
        if (column[k].m_i == piv_row_index) {
            pivot_col_cell_index = k;
            break;
        }
    }
    if (pivot_col_cell_index < 0)
        return false;
        
    if (pivot_col_cell_index != 0) {
        lean_assert(column.size() > 1);
        // swap the pivot column cell with the head cell
        auto c = column[0];
        column[0]  = column[pivot_col_cell_index];
        column[pivot_col_cell_index] = c;

        m_A.m_rows[piv_row_index][column[0].m_offset].m_offset = 0;
        m_A.m_rows[c.m_i][c.m_offset].m_offset = pivot_col_cell_index;
    }
    while (column.size() > 1) {
        auto & c = column.back();
        lean_assert(c.m_i != piv_row_index);
        if(! m_A.pivot_row_to_row_given_cell(piv_row_index, c, j)) {
            return false;
        }
        if (m_pivoted_rows!= nullptr)
            m_pivoted_rows->insert(c.m_i);
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
    for (auto j : m_nbasis) {
        bm.insert(j);
    }
    return bm.size() == m_nbasis.size();
}

template <typename T, typename X> bool lp_core_solver_base<T, X>::
basis_is_correctly_represented_in_heading() const {
    for (unsigned i = 0; i < m_m(); i++) {
        if (m_basis_heading[m_basis[i]] != static_cast<int>(i))
            return false;
    }
    return true;
}
template <typename T, typename X> bool lp_core_solver_base<T, X>::
non_basis_is_correctly_represented_in_heading() const {
    for (unsigned i = 0; i < m_nbasis.size(); i++) {
        if (m_basis_heading[m_nbasis[i]] !=  - static_cast<int>(i) - 1)
            return false;
    }
    for (unsigned j = 0; j < m_A.column_count(); j++) {
        if (m_basis_heading[j] >= 0) {
            lean_assert(static_cast<unsigned>(m_basis_heading[j]) < m_A.row_count() && m_basis[m_basis_heading[j]] == j);
        }
    }
    return true;
}

template <typename T, typename X> bool lp_core_solver_base<T, X>::
    basis_heading_is_correct() const {
    lean_assert(m_basis_heading.size() == m_A.column_count());
    lean_assert(m_basis.size() == m_A.row_count());
    lean_assert(m_nbasis.size() <= m_A.column_count() - m_A.row_count()); // for the dual the size of non basis can be smaller
    if (!basis_has_no_doubles()) {
        //        std::cout << "basis_has_no_doubles" << std::endl;
        return false;
    }

    if (!non_basis_has_no_doubles()) {
        // std::cout << "non_basis_has_no_doubles" << std::endl;
        return false;
    }

    if (!basis_is_correctly_represented_in_heading()) {
        // std::cout << "basis_is_correctly_represented_in_heading" << std::endl;
        return false;
    }

    if (!non_basis_is_correctly_represented_in_heading()) {
        // std::cout << "non_basis_is_correctly_represented_in_heading" << std::endl;
        return false;
    }


    return true;
}

template <typename T, typename X> void lp_core_solver_base<T, X>::
restore_x_and_refactor(int entering, int leaving, X const & t) {
    this->restore_basis_change(entering, leaving);
    restore_x(entering, t);
    init_factorization(m_factorization, m_A, m_basis, m_settings);
    if (m_factorization->get_status() == LU_status::Degenerated) {
        LP_OUT(m_settings,  "cannot refactor" << std::endl);
        m_status = lp_status::FLOATING_POINT_ERROR;
        return;
    }
    //   solve_Ax_eq_b();
    if (A_mult_x_is_off()) {
        LP_OUT(m_settings, "cannot restore solution" << std::endl);
        m_status = lp_status::FLOATING_POINT_ERROR;
        return;
    }
}

template <typename T, typename X> void lp_core_solver_base<T, X>::
restore_x(unsigned entering, X const & t) {
    if (is_zero(t)) return;
    m_x[entering] -= t;
    for (unsigned i : m_ed.m_index) {
        m_x[m_basis[i]]  = m_copy_of_xB[i];
    }
}

template <typename T, typename X> void lp_core_solver_base<T, X>::
fill_reduced_costs_from_m_y_by_rows() {
    unsigned j = m_n();
    while (j--) {
        if (m_basis_heading[j] < 0)
            m_d[j] = m_costs[j];
        else
            m_d[j] = numeric_traits<T>::zero();
    }

    unsigned i = m_m();
    while (i--) {
        const T & y = m_y[i];
        if (is_zero(y)) continue;
        for (row_cell<T> & it : m_A.m_rows[i]) {
            j = it.m_j;
            if (m_basis_heading[j] < 0) {
                m_d[j] -= y * it.get_val();
            }
        }
    }
}

template <typename T, typename X> void lp_core_solver_base<T, X>::
copy_rs_to_xB(vector<X> & rs) {
    unsigned j = m_m();
    while (j--) {
        m_x[m_basis[j]] = rs[j];
    }
}

template <typename T, typename X> std::string lp_core_solver_base<T, X>::
column_name(unsigned column) const {
    return m_column_names.get_column_name(column);
}

template <typename T, typename X> void lp_core_solver_base<T, X>::
copy_right_side(vector<X> & rs) {
    unsigned i = m_m();
    while (i --) {
        rs[i] = m_b[i];
    }
}

template <typename T, typename X> void lp_core_solver_base<T, X>::
add_delta_to_xB(vector<X> & del) {
    unsigned i = m_m();
    while (i--) {
        this->m_x[this->m_basis[i]] -= del[i];
    }
}

template <typename T, typename X> void lp_core_solver_base<T, X>::
find_error_in_BxB(vector<X>& rs){
    unsigned row = m_m();
    while (row--) {
        auto &rsv = rs[row];
        for (auto & it : m_A.m_rows[row]) {
            unsigned j = it.m_j;
            if (m_basis_heading[j] >= 0) {
                rsv -= m_x[j] * it.get_val();
            }
        }
    }
}

// recalculates the projection of x to B, such that Ax = b
template <typename T, typename X> void lp_core_solver_base<T, X>::
solve_Ax_eq_b() {
    if (numeric_traits<X>::precise()) {
        vector<X> rs(m_m());
        rs_minus_Anx(rs);
        m_factorization->solve_By(rs);
        copy_rs_to_xB(rs);
    } else {
        vector<X> rs(m_m());
        rs_minus_Anx(rs);
        vector<X> rrs = rs; // another copy of rs
        m_factorization->solve_By(rs);
        copy_rs_to_xB(rs);
        find_error_in_BxB(rrs);
        m_factorization->solve_By(rrs);
        add_delta_to_xB(rrs);
    }
}




template <typename T, typename X> void lp_core_solver_base<T, X>::
snap_non_basic_x_to_bound_and_free_to_zeroes() {
    for (unsigned j : non_basis()) {
        lean_assert(j < m_x.size());
        switch (m_column_types[j]) {
        case column_type::fixed:
        case column_type::boxed:
        case column_type::low_bound:
            m_x[j] = m_low_bounds[j];
            break;
        case column_type::upper_bound:
            m_x[j] = m_upper_bounds[j];
            break;
        default:
            m_x[j] = zero_of_type<X>();
            break;
        }
    }
}
template <typename T, typename X> void lp_core_solver_base<T, X>::
snap_xN_to_bounds_and_fill_xB() {
    snap_non_basic_x_to_bound();
    solve_Ax_eq_b();
}

template <typename T, typename X> void lp_core_solver_base<T, X>::
snap_xN_to_bounds_and_free_columns_to_zeroes() {
    snap_non_basic_x_to_bound_and_free_to_zeroes();
    solve_Ax_eq_b();
}

template <typename T, typename X> void lp_core_solver_base<T, X>::
init_reduced_costs_for_one_iteration() {
    solve_yB(m_y);
    fill_reduced_costs_from_m_y_by_rows();
}

template <typename T, typename X> non_basic_column_value_position lp_core_solver_base<T, X>::
get_non_basic_column_value_position(unsigned j) const {
    switch (m_column_types[j]) {
    case column_type::fixed:
        return x_is_at_low_bound(j)? at_fixed : not_at_bound;
    case column_type::free_column:
        return free_of_bounds;
    case column_type::boxed:
        return x_is_at_low_bound(j)? at_low_bound :(
                                                    x_is_at_upper_bound(j)? at_upper_bound:
                                                    not_at_bound
                                                    );
    case column_type::low_bound:
        return x_is_at_low_bound(j)? at_low_bound : not_at_bound;
    case column_type::upper_bound:
        return x_is_at_upper_bound(j)? at_upper_bound : not_at_bound;
    default:
        lean_unreachable();
    }
    lean_unreachable();
    return at_low_bound;
}

template <typename T, typename X> void lp_core_solver_base<T, X>::init_lu() {
    init_factorization(this->m_factorization, this->m_A, this->m_basis, this->m_settings);
}

template <typename T, typename X> int lp_core_solver_base<T, X>::pivots_in_column_and_row_are_different(int entering, int leaving) const {
    const T & column_p = this->m_ed[this->m_basis_heading[leaving]];
    const T & row_p = this->m_pivot_row[entering];
    if (is_zero(column_p) || is_zero(row_p)) return true; // pivots cannot be zero
    // the pivots have to have the same sign
    if (column_p < 0) {
        if (row_p > 0)
            return 2;
    } else { // column_p > 0
        if (row_p < 0)
            return 2;
    }
    T diff_normalized = abs((column_p - row_p) / (numeric_traits<T>::one() + abs(row_p)));
    if ( !this->m_settings.abs_val_is_smaller_than_harris_tolerance(diff_normalized / T(10)))
        return 1;
    return 0;
}
template <typename T, typename X>  void lp_core_solver_base<T, X>::transpose_rows_tableau(unsigned i, unsigned j) {
    transpose_basis(i, j);
    m_A.transpose_rows(i, j);
}

template <typename T, typename X>  void lp_core_solver_base<T, X>::pivot_fixed_vars_from_basis() {
    // run over basis and non-basis at the same time
    indexed_vector<T> w(m_basis.size()); // the buffer
    unsigned i = 0; // points to basis
    unsigned j = 0; // points to nonbasis
    for (; i < m_basis.size() && j < m_nbasis.size(); i++) {
        unsigned ii = m_basis[i];
        unsigned jj;

        if (get_column_type(ii) != column_type::fixed) continue;
        while (j < m_nbasis.size()) {
            for (; j < m_nbasis.size(); j++) {
                jj = m_nbasis[j];
                if (get_column_type(jj) != column_type::fixed)
                    break;
            }
            if (j >= m_nbasis.size())
                break;
            j++;
            if (m_factorization->need_to_refactor()) {
                change_basis(jj, ii);
                init_lu();
            } else {
                m_factorization->prepare_entering(jj, w); // to init vector w
                m_factorization->replace_column(zero_of_type<T>(), w, m_basis_heading[ii]);
                change_basis(jj, ii);
            }
            if (m_factorization->get_status() != LU_status::OK) {
                change_basis(ii, jj);
                init_lu();
            } else {
                break;
            }
        }
        lean_assert(m_factorization->get_status()== LU_status::OK);
    }
}

template <typename T, typename X> bool 
lp_core_solver_base<T, X>::infeasibility_costs_are_correct() const {
    if (! this->m_using_infeas_costs)
        return true;
    lean_assert(costs_on_nbasis_are_zeros());
    for (unsigned j :this->m_basis) {
        if (!infeasibility_cost_is_correct_for_column(j)) {
            std::cout << "infeasibility_cost_is_correct_for_column does not hold\n";
            print_column_info(j, std::cout);
            return false;
        }
        if (!is_zero(m_d[j])) {
            std::cout << "m_d is not zero\n";
            print_column_info(j, std::cout);
            return false;
        }
    }
    return true;
}

template <typename T, typename X> bool
lp_core_solver_base<T, X>::infeasibility_cost_is_correct_for_column(unsigned j)  const {
    T r = (!this->m_settings.use_breakpoints_in_feasibility_search)? -one_of_type<T>(): one_of_type<T>();
        
    switch (this->m_column_types[j]) {
    case column_type::fixed:
    case column_type::boxed:
        if (this->x_above_upper_bound(j)) {
            return (this->m_costs[j] == r);
        }
        if (this->x_below_low_bound(j)) {
            return (this->m_costs[j] == -r);
        }
        return is_zero(this->m_costs[j]);

    case column_type::low_bound:
        if (this->x_below_low_bound(j)) {
            return this->m_costs[j] == -r;
        }
        return is_zero(this->m_costs[j]);

    case column_type::upper_bound:
        if (this->x_above_upper_bound(j)) {
            return this->m_costs[j] == r;
        }
        return is_zero(this->m_costs[j]);
    case column_type::free_column:
        return is_zero(this->m_costs[j]);
    default:
        lean_assert(false);
        return true;
    }
}

}
