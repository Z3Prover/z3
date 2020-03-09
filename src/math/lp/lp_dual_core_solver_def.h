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
#include <algorithm>
#include <string>
#include "util/vector.h"
#include "math/lp/lp_dual_core_solver.h"

namespace lp {

template <typename T, typename X> void lp_dual_core_solver<T, X>::init_a_wave_by_zeros() {
    unsigned j = this->m_m();
    while (j--) {
        m_a_wave[j] = numeric_traits<T>::zero();
    }
}

template <typename T, typename X> void lp_dual_core_solver<T, X>::restore_non_basis() {
    auto & nb = this->m_nbasis;
    nb.reset();
    unsigned j = this->m_n();
    while (j--) {
        if (this->m_basis_heading[j] >= 0 ) continue;
        if (m_can_enter_basis[j]) {
            lp_assert(std::find(nb.begin(), nb.end(), j) == nb.end());
            nb.push_back(j);
            this->m_basis_heading[j] = - static_cast<int>(nb.size());
        }
    }
}

template <typename T, typename X> bool lp_dual_core_solver<T, X>::update_basis(int entering, int leaving) {
    // the second argument is the element of the entering column from the pivot row - its value should be equal to the low diagonal element of the bump after all pivoting is done
    if (this->m_refactor_counter++ < 200) {
        this->m_factorization->replace_column(this->m_ed[this->m_factorization->basis_heading(leaving)], this->m_w);
        if (this->m_factorization->get_status() == LU_status::OK) {
            this->m_factorization->change_basis(entering, leaving);
            return true;
        }
    }
    // need to refactor
    this->m_factorization->change_basis(entering, leaving);
    init_factorization(this->m_factorization, this->m_A, this->m_basis, this->m_basis_heading, this->m_settings);
    this->m_refactor_counter = 0;
    if (this->m_factorization->get_status() != LU_status::OK) {
        LP_OUT(this->m_settings, "failing refactor for entering = " << entering << ", leaving = " << leaving << " total_iterations = " << this->total_iterations() << std::endl);
        this->m_iters_with_no_cost_growing++;
        return false;
    }
    return true;
}

template <typename T, typename X> void lp_dual_core_solver<T, X>::recalculate_xB_and_d() {
    this->solve_Ax_eq_b();
    recalculate_d();
}

template <typename T, typename X> void lp_dual_core_solver<T, X>::recalculate_d() {
    this->solve_yB(this->m_y);
    this->fill_reduced_costs_from_m_y_by_rows();
}

template <typename T, typename X> void lp_dual_core_solver<T, X>::init_betas() {
    // todo : look at page 194 of Progress in the dual simplex algorithm for solving large scale LP problems : techniques for a fast and stable implementation
    // the current implementation is not good enough: todo
    unsigned i = this->m_m();
    while (i--) {
        m_betas[i] = 1;
    }
}

template <typename T, typename X> void lp_dual_core_solver<T, X>::adjust_xb_for_changed_xn_and_init_betas() {
    this->solve_Ax_eq_b();
    init_betas();
}

template <typename T, typename X> void lp_dual_core_solver<T, X>::start_with_initial_basis_and_make_it_dual_feasible() {
    this->set_non_basic_x_to_correct_bounds(); // It is not an efficient version, see 3.29,
    // however this version does not require that m_x is the solution of Ax = 0 beforehand
    adjust_xb_for_changed_xn_and_init_betas();
}

template <typename T, typename X> bool lp_dual_core_solver<T, X>::done() {
    if (this->get_status() == lp_status::OPTIMAL) {
        return true;
    }
    if (this->total_iterations() > this->m_settings.max_total_number_of_iterations) { // debug !!!!
        this->set_status(lp_status::ITERATIONS_EXHAUSTED);
        return true;
    }
    return false; // todo, need to be more cases
}

template <typename T, typename X> T lp_dual_core_solver<T, X>::get_edge_steepness_for_lower_bound(unsigned p) {
    lp_assert(this->m_basis_heading[p] >= 0 && static_cast<unsigned>(this->m_basis_heading[p]) < this->m_m());
    T del = this->m_x[p] - this->m_lower_bounds[p];
    del *= del;
    return del / this->m_betas[this->m_basis_heading[p]];
}

template <typename T, typename X> T lp_dual_core_solver<T, X>::get_edge_steepness_for_upper_bound(unsigned p) {
    lp_assert(this->m_basis_heading[p] >= 0 && static_cast<unsigned>(this->m_basis_heading[p]) < this->m_m());
    T del = this->m_x[p] - this->m_upper_bounds[p];
    del *= del;
    return del / this->m_betas[this->m_basis_heading[p]];
}

template <typename T, typename X> T lp_dual_core_solver<T, X>::pricing_for_row(unsigned i) {
    unsigned p = this->m_basis[i];
    switch (this->m_column_types[p]) {
    case column_type::fixed:
    case column_type::boxed:
        if (this->x_below_low_bound(p)) {
            T del =  get_edge_steepness_for_lower_bound(p);
            return del;
        }
        if (this->x_above_upper_bound(p)) {
            T del =  get_edge_steepness_for_upper_bound(p);
            return del;
        }
        return numeric_traits<T>::zero();
    case column_type::lower_bound:
        if (this->x_below_low_bound(p)) {
            T del =  get_edge_steepness_for_lower_bound(p);
            return del;
        }
        return numeric_traits<T>::zero();
        break;
    case column_type::upper_bound:
        if (this->x_above_upper_bound(p)) {
            T del =  get_edge_steepness_for_upper_bound(p);
            return del;
        }
        return numeric_traits<T>::zero();
        break;
    case column_type::free_column:
        lp_assert(numeric_traits<T>::is_zero(this->m_d[p]));
        return numeric_traits<T>::zero();
    default:
        lp_unreachable();
    }
    lp_unreachable();
    return numeric_traits<T>::zero();
}

template <typename T, typename X> void lp_dual_core_solver<T, X>::pricing_loop(unsigned number_of_rows_to_try, unsigned offset_in_rows) {
    m_r = -1;
    T steepest_edge_max = numeric_traits<T>::zero();
    unsigned initial_offset_in_rows = offset_in_rows;
    unsigned i = offset_in_rows;
    unsigned rows_left = number_of_rows_to_try;
    do  {
        if (m_forbidden_rows.find(i) != m_forbidden_rows.end()) {
            if (++i == this->m_m()) {
                i = 0;
            }
            continue;
        }
        T se = pricing_for_row(i);
        if (se > steepest_edge_max) {
            steepest_edge_max = se;
            m_r = i;
            if (rows_left > 0) {
                rows_left--;
            }
        }
        if (++i == this->m_m()) {
            i = 0;
        }
    } while (i != initial_offset_in_rows && rows_left);
    if (m_r == -1) {
        if (this->get_status() != lp_status::UNSTABLE) {
            this->set_status(lp_status::OPTIMAL);
        }
    } else {
        m_p = this->m_basis[m_r];
        m_delta = get_delta();
        if (advance_on_known_p()){
            m_forbidden_rows.clear();
            return;
        }
        // failure in advance_on_known_p
        if (this->get_status() == lp_status::FLOATING_POINT_ERROR) {
            return;
        }
        this->set_status(lp_status::UNSTABLE);
        m_forbidden_rows.insert(m_r);
    }
}

    // this calculation is needed for the steepest edge update,
    // it hijackes m_pivot_row_of_B_1 for this purpose since we will need it anymore to the end of the cycle
template <typename T, typename X> void lp_dual_core_solver<T, X>::DSE_FTran() { // todo, see algorithm 7 from page 35
    this->m_factorization->solve_By_for_T_indexed_only(this->m_pivot_row_of_B_1, this->m_settings);
}

template <typename T, typename X> bool lp_dual_core_solver<T, X>::advance_on_known_p() {
    if (done()) {
        return true;
    }
    this->calculate_pivot_row_of_B_1(m_r);
    this->calculate_pivot_row_when_pivot_row_of_B1_is_ready(m_r);
    if (!ratio_test()) {
        return true;
    }
    calculate_beta_r_precisely();
    this->solve_Bd(m_q); // FTRAN
    int pivot_compare_result = this->pivots_in_column_and_row_are_different(m_q, m_p);
    if (!pivot_compare_result){;}
    else if (pivot_compare_result == 2) { // the sign is changed, cannot continue
        lp_unreachable(); // not implemented yet
    } else {
        lp_assert(pivot_compare_result == 1);
        this->init_lu();
    }
    DSE_FTran();
    return basis_change_and_update();
}

template <typename T, typename X> int lp_dual_core_solver<T, X>::define_sign_of_alpha_r() {
    switch (this->m_column_types[m_p]) {
    case column_type::boxed:
    case column_type::fixed:
        if (this->x_below_low_bound(m_p)) {
            return -1;
        }
        if (this->x_above_upper_bound(m_p)) {
            return 1;
        }
        lp_unreachable();
    case column_type::lower_bound:
        if (this->x_below_low_bound(m_p)) {
            return -1;
        }
        lp_unreachable();
    case column_type::upper_bound:
        if (this->x_above_upper_bound(m_p)) {
            return 1;
        }
        lp_unreachable();
    default:
        lp_unreachable();
    }
    lp_unreachable();
    return 0;
}

template <typename T, typename X> bool lp_dual_core_solver<T, X>::can_be_breakpoint(unsigned j) {
    if (this->pivot_row_element_is_too_small_for_ratio_test(j)) return false;
    switch (this->m_column_types[j]) {
    case column_type::lower_bound:
        lp_assert(this->m_settings.abs_val_is_smaller_than_harris_tolerance(this->m_x[j] - this->m_lower_bounds[j]));
        return m_sign_of_alpha_r * this->m_pivot_row[j]  > 0;
    case column_type::upper_bound:
        lp_assert(this->m_settings.abs_val_is_smaller_than_harris_tolerance(this->m_x[j] - this->m_upper_bounds[j]));
        return m_sign_of_alpha_r * this->m_pivot_row[j] < 0;
    case column_type::boxed:
        {
            bool lower_bound = this->x_is_at_lower_bound(j);
            bool grawing = m_sign_of_alpha_r * this->m_pivot_row[j] > 0;
            return lower_bound == grawing;
        }
    case column_type::fixed: // is always dual feasible so we ignore it
        return false;
    case column_type::free_column:
        return true;
    default:
        return false;
    }
}

template <typename T, typename X> void lp_dual_core_solver<T, X>::fill_breakpoint_set() {
    m_breakpoint_set.clear();
    for (unsigned j : this->non_basis()) {
        if (can_be_breakpoint(j)) {
            m_breakpoint_set.insert(j);
        }
    }
}

// template <typename T, typename X> void lp_dual_core_solver<T, X>::FTran() {
//     this->solve_Bd(m_q);
// }

template <typename T, typename X> T lp_dual_core_solver<T, X>::get_delta() {
    switch (this->m_column_types[m_p]) {
    case column_type::boxed:
        if (this->x_below_low_bound(m_p)) {
            return this->m_x[m_p] - this->m_lower_bounds[m_p];
        }
        if (this->x_above_upper_bound(m_p)) {
            return this->m_x[m_p] - this->m_upper_bounds[m_p];
        }
        lp_unreachable();
    case column_type::lower_bound:
        if (this->x_below_low_bound(m_p)) {
            return this->m_x[m_p] - this->m_lower_bounds[m_p];
        }
        lp_unreachable();
    case column_type::upper_bound:
        if (this->x_above_upper_bound(m_p)) {
            return get_edge_steepness_for_upper_bound(m_p);
        }
        lp_unreachable();
    case column_type::fixed:
        return this->m_x[m_p] - this->m_upper_bounds[m_p];
    default:
        lp_unreachable();
    }
    lp_unreachable();
    return zero_of_type<T>();
}

template <typename T, typename X> void lp_dual_core_solver<T, X>::restore_d() {
    this->m_d[m_p] = numeric_traits<T>::zero();
    for (auto j : this->non_basis()) {
        this->m_d[j] += m_theta_D * this->m_pivot_row[j];
    }
}

template <typename T, typename X> bool lp_dual_core_solver<T, X>::d_is_correct() {
    this->solve_yB(this->m_y);
    for  (auto j : this->non_basis()) {
        T d = this->m_costs[j] -  this->m_A.dot_product_with_column(this->m_y, j);
        if (numeric_traits<T>::get_double(abs(d - this->m_d[j])) >= 0.001) {
            LP_OUT(this->m_settings, "total_iterations = " << this->total_iterations() << std::endl
                << "d[" << j << "] = " << this->m_d[j] << " but should be " << d << std::endl);
            return false;
        }
    }
    return true;
}

template <typename T, typename X> void lp_dual_core_solver<T, X>::xb_minus_delta_p_pivot_column() {
    unsigned i = this->m_m();
    while (i--) {
        this->m_x[this->m_basis[i]] -= m_theta_P * this->m_ed[i];
    }
}

template <typename T, typename X> void lp_dual_core_solver<T, X>::update_betas() { // page 194 of Progress ... todo - once in a while betas have to be reinitialized
    T one_over_arq = numeric_traits<T>::one() / this->m_pivot_row[m_q];
    T beta_r = this->m_betas[m_r] = std::max(T(0.0001), (m_betas[m_r] * one_over_arq) *  one_over_arq);
    T k = -2 * one_over_arq;
    unsigned i = this->m_m();
    while (i--) {
        if (static_cast<int>(i) == m_r) continue;
        T a = this->m_ed[i];
        m_betas[i] += a * (a * beta_r + k * this->m_pivot_row_of_B_1[i]);
        if (m_betas[i] < T(0.0001))
            m_betas[i] = T(0.0001);
    }
}

template <typename T, typename X> void lp_dual_core_solver<T, X>::apply_flips() {
    for (unsigned j : m_flipped_boxed) {
        lp_assert(this->x_is_at_bound(j));
        if (this->x_is_at_lower_bound(j)) {
            this->m_x[j] = this->m_upper_bounds[j];
        } else {
            this->m_x[j] = this->m_lower_bounds[j];
        }
    }
}

template <typename T, typename X> void lp_dual_core_solver<T, X>::snap_xN_column_to_bounds(unsigned j) {
    switch (this->m_column_type[j]) {
    case column_type::fixed:
        this->m_x[j] = this->m_lower_bounds[j];
        break;
    case column_type::boxed:
        if (this->x_is_at_lower_bound(j)) {
            this->m_x[j] = this->m_lower_bounds[j];
        } else {
            this->m_x[j] = this->m_upper_bounds[j];
        }
        break;
    case column_type::lower_bound:
        this->m_x[j] = this->m_lower_bounds[j];
        break;
    case column_type::upper_bound:
        this->m_x[j] = this->m_upper_bounds[j];
        break;
    case column_type::free_column:
        break;
    default:
        lp_unreachable();
    }
}

template <typename T, typename X> void lp_dual_core_solver<T, X>::snap_xN_to_bounds() {
    for (auto j : this->non_basis()) {
        snap_xN_column_to_bounds(j);
    }
}

template <typename T, typename X> void lp_dual_core_solver<T, X>::init_beta_precisely(unsigned i) {
    vector<T> vec(this->m_m(), numeric_traits<T>::zero());
    vec[i] = numeric_traits<T>::one();
    this->m_factorization->solve_yB_with_error_check(vec, this->m_basis);
    T beta = numeric_traits<T>::zero();
    for (T & v : vec) {
        beta += v * v;
    }
    this->m_betas[i] =beta;
}

template <typename T, typename X> void lp_dual_core_solver<T, X>::init_betas_precisely() {
    unsigned i = this->m_m();
    while (i--) {
        init_beta_precisely(i);
    }
}

// step 7 of the algorithm from Progress
template <typename T, typename X> bool lp_dual_core_solver<T, X>::basis_change_and_update() {
    update_betas();
    update_d_and_xB();
    //    m_theta_P = m_delta / this->m_ed[m_r];
    m_theta_P = m_delta / this->m_pivot_row[m_q];
    //    xb_minus_delta_p_pivot_column();
    apply_flips();
    if (!this->update_basis_and_x(m_q, m_p, m_theta_P)) {
          init_betas_precisely();
          return false;
    }

    if (snap_runaway_nonbasic_column(m_p)) {
        if (!this->find_x_by_solving()) {
            revert_to_previous_basis();
            this->iters_with_no_cost_growing()++;
            return false;
        }
    }

    if (!problem_is_dual_feasible()) {
        // todo : shift the costs!!!!
        revert_to_previous_basis();
        this->iters_with_no_cost_growing()++;
        return false;
    }

    lp_assert(d_is_correct());
    return true;
}

template <typename T, typename X> void lp_dual_core_solver<T, X>::recover_leaving() {
    switch (m_entering_boundary_position) {
    case at_lower_bound:
    case at_fixed:
        this->m_x[m_q] = this->m_lower_bounds[m_q];
        break;
    case at_upper_bound:
        this->m_x[m_q] = this->m_upper_bounds[m_q];
        break;
    case free_of_bounds:
        this->m_x[m_q] = zero_of_type<X>();
    default:
        lp_unreachable();
    }
}

template <typename T, typename X> void lp_dual_core_solver<T, X>::revert_to_previous_basis() {
    LP_OUT(this->m_settings, "revert to previous basis on ( " << m_p << ", " << m_q << ")" << std::endl);
    this->change_basis_unconditionally(m_p, m_q);
    init_factorization(this->m_factorization, this->m_A, this->m_basis, this->m_settings);
    if (this->m_factorization->get_status() != LU_status::OK) {
        this->set_status(lp_status::FLOATING_POINT_ERROR); // complete failure
        return;
    }
    recover_leaving();
    if (!this->find_x_by_solving()) {
        this->set_status(lp_status::FLOATING_POINT_ERROR);
        return;
    }
    recalculate_xB_and_d();
    init_betas_precisely();
}

// returns true if the column has been snapped
template <typename T, typename X> bool lp_dual_core_solver<T, X>::snap_runaway_nonbasic_column(unsigned j) {
    switch (this->m_column_types[j]) {
    case column_type::fixed:
    case column_type::lower_bound:
        if (!this->x_is_at_lower_bound(j)) {
            this->m_x[j] = this->m_lower_bounds[j];
            return true;
        }
        break;
    case column_type::boxed:
        {
            bool closer_to_lower_bound = abs(this->m_lower_bounds[j] - this->m_x[j]) < abs(this->m_upper_bounds[j] - this->m_x[j]);
            if (closer_to_lower_bound) {
                if (!this->x_is_at_lower_bound(j)) {
                    this->m_x[j] = this->m_lower_bounds[j];
                    return true;
                }
            } else {
                if (!this->x_is_at_upper_bound(j)) {
                    this->m_x[j] = this->m_lower_bounds[j];
                    return true;
                }
            }
        }
        break;
    case column_type::upper_bound:
        if (!this->x_is_at_upper_bound(j)) {
            this->m_x[j] = this->m_upper_bounds[j];
            return true;
        }
        break;
    default:
        break;
    }
    return false;
}


template <typename T, typename X> bool lp_dual_core_solver<T, X>::problem_is_dual_feasible() const {
    for (unsigned j : this->non_basis()){
        if (!this->column_is_dual_feasible(j)) {
            return false;
        }
    }
    return true;
}

template <typename T, typename X> unsigned lp_dual_core_solver<T, X>::get_number_of_rows_to_try_for_leaving() {
    unsigned s = this->m_m();
    if (this->m_m() > 300) {
        s = (unsigned)((s / 100.0) * this->m_settings.percent_of_entering_to_check);
    }
    return this->m_settings.random_next() % s + 1;
}

template <typename T, typename X> bool lp_dual_core_solver<T, X>::delta_keeps_the_sign(int initial_delta_sign, const T & delta) {
    if (numeric_traits<T>::precise())
        return ((delta > numeric_traits<T>::zero()) && (initial_delta_sign == 1)) ||
            ((delta < numeric_traits<T>::zero()) && (initial_delta_sign == -1));

    double del = numeric_traits<T>::get_double(delta);
    return ( (del > this->m_settings.zero_tolerance) && (initial_delta_sign == 1)) ||
        ((del < - this->m_settings.zero_tolerance) && (initial_delta_sign == -1));
}

template <typename T, typename X> void lp_dual_core_solver<T, X>::set_status_to_tentative_dual_unbounded_or_dual_unbounded() {
    if (this->get_status() == lp_status::TENTATIVE_DUAL_UNBOUNDED) {
        this->set_status(lp_status::DUAL_UNBOUNDED);
    } else {
        this->set_status(lp_status::TENTATIVE_DUAL_UNBOUNDED);
    }
}

template <typename T, typename X> void lp_dual_core_solver<T, X>::add_tight_breakpoints_and_q_to_flipped_set() {
    m_flipped_boxed.insert(m_q);
    for (auto j : m_tight_set) {
        m_flipped_boxed.insert(j);
    }
}

template <typename T, typename X> T lp_dual_core_solver<T, X>::delta_lost_on_flips_of_tight_breakpoints() {
    T ret = abs(this->bound_span(m_q) * this->m_pivot_row[m_q]);
    for (auto j : m_tight_set) {
        ret += abs(this->bound_span(j) * this->m_pivot_row[j]);
    }
    return ret;
}

template <typename T, typename X> bool lp_dual_core_solver<T, X>::tight_breakpoinst_are_all_boxed() {
    if (this->m_column_types[m_q] != column_type::boxed) return false;
    for (auto j : m_tight_set) {
        if (this->m_column_types[j] != column_type::boxed) return false;
    }
    return true;
}

template <typename T, typename X> T lp_dual_core_solver<T, X>::calculate_harris_delta_on_breakpoint_set() {
    bool first_time = true;
    T ret = zero_of_type<T>();
    lp_assert(m_breakpoint_set.size() > 0);
    for (auto j : m_breakpoint_set) {
        T t;
        if (this->x_is_at_lower_bound(j)) {
            t = abs((std::max(this->m_d[j], numeric_traits<T>::zero()) + m_harris_tolerance) / this->m_pivot_row[j]);
        } else {
            t = abs((std::min(this->m_d[j], numeric_traits<T>::zero()) - m_harris_tolerance) / this->m_pivot_row[j]);
        }
        if (first_time) {
            ret = t;
            first_time = false;
        } else if (t < ret) {
            ret = t;
        }
    }
    return ret;
}

template <typename T, typename X> void lp_dual_core_solver<T, X>::fill_tight_set_on_harris_delta(const T & harris_delta ){
    m_tight_set.clear();
    for (auto j : m_breakpoint_set) {
        if (this->x_is_at_lower_bound(j)) {
            if (abs(std::max(this->m_d[j], numeric_traits<T>::zero()) / this->m_pivot_row[j]) <= harris_delta){
                m_tight_set.insert(j);
            }
        } else {
            if (abs(std::min(this->m_d[j], numeric_traits<T>::zero() ) / this->m_pivot_row[j]) <= harris_delta){
                m_tight_set.insert(j);
            }
        }
    }
}

template <typename T, typename X> void lp_dual_core_solver<T, X>::find_q_on_tight_set() {
    m_q = -1;
    T max_pivot;
    for (auto j : m_tight_set) {
        T r = abs(this->m_pivot_row[j]);
        if (m_q != -1) {
            if (r > max_pivot) {
                max_pivot = r;
                m_q = j;
            }
        } else {
            max_pivot = r;
            m_q = j;
        }
    }
    m_tight_set.erase(m_q);
    lp_assert(m_q != -1);
}

template <typename T, typename X> void lp_dual_core_solver<T, X>::find_q_and_tight_set() {
    T harris_del = calculate_harris_delta_on_breakpoint_set();
    fill_tight_set_on_harris_delta(harris_del);
    find_q_on_tight_set();
    m_entering_boundary_position = this->get_non_basic_column_value_position(m_q);
}

template <typename T, typename X> void lp_dual_core_solver<T, X>::erase_tight_breakpoints_and_q_from_breakpoint_set() {
    m_breakpoint_set.erase(m_q);
    for (auto j : m_tight_set) {
        m_breakpoint_set.erase(j);
    }
}

template <typename T, typename X> bool lp_dual_core_solver<T, X>::ratio_test() {
    m_sign_of_alpha_r = define_sign_of_alpha_r();
    fill_breakpoint_set();
    m_flipped_boxed.clear();
    int initial_delta_sign = m_delta >= numeric_traits<T>::zero()? 1: -1;
    do {
        if (m_breakpoint_set.empty()) {
            set_status_to_tentative_dual_unbounded_or_dual_unbounded();
            return false;
        }
        this->set_status(lp_status::FEASIBLE);
        find_q_and_tight_set();
        if (!tight_breakpoinst_are_all_boxed())  break;
        T del = m_delta - delta_lost_on_flips_of_tight_breakpoints() * initial_delta_sign;
        if (!delta_keeps_the_sign(initial_delta_sign, del)) break;
        if (m_tight_set.size() + 1 == m_breakpoint_set.size()) {
            break; // deciding not to flip since we might get stuck without finding m_q, the column entering the basis
        }
        // we can flip m_q together with the tight set and look for another breakpoint candidate for m_q and another tight set
        add_tight_breakpoints_and_q_to_flipped_set();
        m_delta = del;
        erase_tight_breakpoints_and_q_from_breakpoint_set();
    } while (true);
    m_theta_D = this->m_d[m_q] / this->m_pivot_row[m_q];
    return true;
}

template <typename T, typename X> void lp_dual_core_solver<T, X>::process_flipped() {
    init_a_wave_by_zeros();
    for (auto j : m_flipped_boxed) {
        update_a_wave(signed_span_of_boxed(j), j);
    }
}
template <typename T, typename X> void lp_dual_core_solver<T, X>::update_d_and_xB() {
    for (auto j : this->non_basis()) {
        this->m_d[j] -= m_theta_D * this->m_pivot_row[j];
    }
    this->m_d[m_p] = - m_theta_D;
    if (!m_flipped_boxed.empty()) {
        process_flipped();
        update_xb_after_bound_flips();
    }
}

template <typename T, typename X> void lp_dual_core_solver<T, X>::calculate_beta_r_precisely() {
    T t = numeric_traits<T>::zero();
    unsigned i = this->m_m();
    while (i--) {
        T b = this->m_pivot_row_of_B_1[i];
        t += b * b;
    }
    m_betas[m_r] = t;
}
// see "Progress in the dual simplex method for large scale LP problems: practical dual phase 1 algorithms"

template <typename T, typename X> void lp_dual_core_solver<T, X>::update_xb_after_bound_flips() {
    this->m_factorization->solve_By(m_a_wave);
    unsigned i = this->m_m();
    while (i--) {
        this->m_x[this->m_basis[i]] -= m_a_wave[i];
    }
}

template <typename T, typename X> void lp_dual_core_solver<T, X>::one_iteration() {
    unsigned number_of_rows_to_try = get_number_of_rows_to_try_for_leaving();
    unsigned offset_in_rows = this->m_settings.random_next() % this->m_m();
    if (this->get_status() == lp_status::TENTATIVE_DUAL_UNBOUNDED) {
        number_of_rows_to_try = this->m_m();
    } else {
        this->set_status(lp_status::FEASIBLE);
    }
    pricing_loop(number_of_rows_to_try, offset_in_rows);
    lp_assert(problem_is_dual_feasible());
}

template <typename T, typename X> void lp_dual_core_solver<T, X>::solve() { // see the page 35
    lp_assert(d_is_correct());
    lp_assert(problem_is_dual_feasible());
    lp_assert(this->basis_heading_is_correct());
    //this->set_total_iterations(0);
    this->iters_with_no_cost_growing() = 0;
    do {
        if (this->print_statistics_with_iterations_and_nonzeroes_and_cost_and_check_that_the_time_is_over("", *this->m_settings.get_message_ostream())){
            return;
        }
        one_iteration();
    } while (this->get_status() != lp_status::FLOATING_POINT_ERROR && this->get_status() != lp_status::DUAL_UNBOUNDED && this->get_status() != lp_status::OPTIMAL &&
             this->iters_with_no_cost_growing() <= this->m_settings.max_number_of_iterations_with_no_improvements
             && this->total_iterations() <= this->m_settings.max_total_number_of_iterations);
}
}
