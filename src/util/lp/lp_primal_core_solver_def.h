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
#include <list>
#include "util/vector.h"
#include <fstream>
#include <algorithm>
#include <set>
#include <string>
#include "util/lp/lp_primal_core_solver.h"
namespace lp {
// This core solver solves (Ax=b, lower_bound_values \leq x \leq upper_bound_values, maximize costs*x )
// The right side b is given implicitly by x and the basis

template <typename T, typename X>
void lp_primal_core_solver<T, X>::sort_non_basis_rational() {
    lp_assert(numeric_traits<T>::precise());
    if (this->m_settings.use_tableau()) {
        std::sort(this->m_nbasis.begin(), this->m_nbasis.end(), [this](unsigned a, unsigned b) {
                unsigned ca = this->m_A.number_of_non_zeroes_in_column(a);
                unsigned cb = this->m_A.number_of_non_zeroes_in_column(b);
                if (ca == 0 && cb != 0) return false;
                return ca < cb;
            });
    } else {
    std::sort(this->m_nbasis.begin(), this->m_nbasis.end(), [this](unsigned a, unsigned b) {
            unsigned ca = this->m_columns_nz[a];
            unsigned cb = this->m_columns_nz[b];
            if (ca == 0 && cb != 0) return false;
            return ca < cb;
        });}

    m_non_basis_list.clear();
    // reinit m_basis_heading
    for (unsigned j = 0; j < this->m_nbasis.size(); j++) {
        unsigned col = this->m_nbasis[j];
        this->m_basis_heading[col] = - static_cast<int>(j) - 1;
        m_non_basis_list.push_back(col);
    }
}


template <typename T, typename X>
void lp_primal_core_solver<T, X>::sort_non_basis() {
    if (numeric_traits<T>::precise()) {
        sort_non_basis_rational();
        return;
    }
    for (unsigned j : this->m_nbasis) {
        T const & da = this->m_d[j];
        this->m_steepest_edge_coefficients[j] = da * da / this->m_column_norms[j];
    }
    std::sort(this->m_nbasis.begin(), this->m_nbasis.end(), [this](unsigned a, unsigned b) {
            return this->m_steepest_edge_coefficients[a] > this->m_steepest_edge_coefficients[b];
    });

    m_non_basis_list.clear();
    // reinit m_basis_heading
    for (unsigned j = 0; j < this->m_nbasis.size(); j++) {
        unsigned col = this->m_nbasis[j];
        this->m_basis_heading[col] = - static_cast<int>(j) - 1;
        m_non_basis_list.push_back(col);
    }
}

template <typename T, typename X>
bool lp_primal_core_solver<T, X>::column_is_benefitial_for_entering_on_breakpoints(unsigned j) const {
    bool ret;
    const T & d = this->m_d[j];
    switch (this->m_column_types[j]) {
    case column_type::lower_bound:
        lp_assert(this->x_is_at_lower_bound(j));
        ret = d < -m_epsilon_of_reduced_cost;
        break;
    case column_type::upper_bound:
        lp_assert(this->x_is_at_upper_bound(j));
        ret = d > m_epsilon_of_reduced_cost;
        break;
    case column_type::fixed:
        ret = false;
        break;
    case column_type::boxed:
        {
            bool lower_bound = this->x_is_at_lower_bound(j);
            lp_assert(lower_bound || this->x_is_at_upper_bound(j));
            ret = (lower_bound && d < -m_epsilon_of_reduced_cost) || ((!lower_bound) && d > m_epsilon_of_reduced_cost);
        }
        break;
    case column_type::free_column:
        ret = d > m_epsilon_of_reduced_cost || d < - m_epsilon_of_reduced_cost;
        break;
    default:
        lp_unreachable();
        ret = false;
        break;
    }
    return ret;
}
template <typename T, typename X>
bool lp_primal_core_solver<T, X>::column_is_benefitial_for_entering_basis(unsigned j) const {
    if (numeric_traits<T>::precise())
        return column_is_benefitial_for_entering_basis_precise(j);
    if (this->m_using_infeas_costs && this->m_settings.use_breakpoints_in_feasibility_search)
        return column_is_benefitial_for_entering_on_breakpoints(j);
    const T& dj = this->m_d[j];
    switch (this->m_column_types[j]) {
    case column_type::fixed:  break;
    case column_type::free_column:
        if (dj > m_epsilon_of_reduced_cost || dj < -m_epsilon_of_reduced_cost)
            return true;
        break;
    case column_type::lower_bound:
        if (dj > m_epsilon_of_reduced_cost) return true;;
        break;
    case column_type::upper_bound:
        if (dj < -m_epsilon_of_reduced_cost) return true;
        break;
    case column_type::boxed:
        if (dj > m_epsilon_of_reduced_cost) {
            if (this->m_x[j] < this->m_upper_bounds[j] - this->bound_span(j)/2)
                return true;
            break;
        } else if (dj < - m_epsilon_of_reduced_cost) {
            if (this->m_x[j] > this->m_lower_bounds[j] + this->bound_span(j)/2)
                return true;
        }
        break;
    default:
        lp_unreachable();
        break;
    }
    return false;
}
template <typename T, typename X>
bool lp_primal_core_solver<T, X>::column_is_benefitial_for_entering_basis_precise(unsigned j) const {
    lp_assert (numeric_traits<T>::precise());
    if (this->m_using_infeas_costs && this->m_settings.use_breakpoints_in_feasibility_search)
        return column_is_benefitial_for_entering_on_breakpoints(j);    
    const T& dj = this->m_d[j];
    TRACE("lar_solver", tout << "dj=" << dj << "\n";); 
    switch (this->m_column_types[j]) {
    case column_type::fixed:  break;
    case column_type::free_column:
        if (!is_zero(dj))
            return true;
        break;
    case column_type::lower_bound:
        if (dj > zero_of_type<T>()) return true;
        if (dj < 0 && this->m_x[j] > this->m_lower_bounds[j]){
            return true;
        }
        break;
    case column_type::upper_bound:
        if (dj < zero_of_type<T>()) return true;
        if (dj > 0 && this->m_x[j] < this->m_upper_bounds[j]) {
            return true;
        }
        break;
    case column_type::boxed:
        if (dj > zero_of_type<T>()) {
            if (this->m_x[j] < this->m_upper_bounds[j])
                return true;
            break;
        } else if (dj < zero_of_type<T>()) {
            if (this->m_x[j] > this->m_lower_bounds[j])
                return true;
        }
        break;
    default:
        lp_unreachable();
        break;
    }
    return false;
}

template <typename T, typename X>
int lp_primal_core_solver<T, X>::choose_entering_column_presize(unsigned number_of_benefitial_columns_to_go_over) { // at this moment m_y = cB * B(-1)
    lp_assert(numeric_traits<T>::precise());
    if (number_of_benefitial_columns_to_go_over == 0)
        return -1;
    if (this->m_basis_sort_counter == 0) {
        sort_non_basis();
        this->m_basis_sort_counter = 20;
    }
    else {
        this->m_basis_sort_counter--;
    }
    unsigned j_nz = this->m_m() + 1; // this number is greater than the max column size
    std::list<unsigned>::iterator entering_iter = m_non_basis_list.end();
    for (auto non_basis_iter = m_non_basis_list.begin(); number_of_benefitial_columns_to_go_over && non_basis_iter != m_non_basis_list.end(); ++non_basis_iter) {
        unsigned j = *non_basis_iter;
        if (!column_is_benefitial_for_entering_basis(j))
            continue;

        // if we are here then j is a candidate to enter the basis
        unsigned t = this->m_columns_nz[j];
        if (t < j_nz) {
            j_nz = t;
            entering_iter = non_basis_iter;
            if (number_of_benefitial_columns_to_go_over)
                number_of_benefitial_columns_to_go_over--;
        } else if (t == j_nz && this->m_settings.random_next() % 2 == 0) {
            entering_iter = non_basis_iter;
        }
    }// while (number_of_benefitial_columns_to_go_over && initial_offset_in_non_basis != offset_in_nb);
    if (entering_iter == m_non_basis_list.end())
        return -1;
    unsigned entering = *entering_iter;
    m_sign_of_entering_delta = this->m_d[entering] > 0 ? 1 : -1;
    if (this->m_using_infeas_costs && this->m_settings.use_breakpoints_in_feasibility_search)
        m_sign_of_entering_delta = -m_sign_of_entering_delta;
    m_non_basis_list.erase(entering_iter);
    m_non_basis_list.push_back(entering);
    return entering;
}


template <typename T, typename X>
int lp_primal_core_solver<T, X>::choose_entering_column(unsigned number_of_benefitial_columns_to_go_over) { // at this moment m_y = cB * B(-1)
    if (numeric_traits<T>::precise())
        return choose_entering_column_presize(number_of_benefitial_columns_to_go_over);
    if (number_of_benefitial_columns_to_go_over == 0)
        return -1;
    if (this->m_basis_sort_counter == 0) {
        sort_non_basis();
        this->m_basis_sort_counter = 20;
    } else {
        this->m_basis_sort_counter--;
    }
    T steepest_edge = zero_of_type<T>();
    std::list<unsigned>::iterator entering_iter = m_non_basis_list.end();
    for (auto non_basis_iter= m_non_basis_list.begin(); number_of_benefitial_columns_to_go_over && non_basis_iter != m_non_basis_list.end(); ++non_basis_iter) {
        unsigned j = *non_basis_iter;
        if (!column_is_benefitial_for_entering_basis(j))
            continue;

        // if we are here then j is a candidate to enter the basis
        T dj = this->m_d[j];
        T t = dj * dj / this->m_column_norms[j];
        if (t > steepest_edge) {
            steepest_edge = t;
            entering_iter = non_basis_iter;
            if (number_of_benefitial_columns_to_go_over)
                number_of_benefitial_columns_to_go_over--;
        }
    }// while (number_of_benefitial_columns_to_go_over && initial_offset_in_non_basis != offset_in_nb);
    if (entering_iter != m_non_basis_list.end()) {
        unsigned entering = *entering_iter;
        m_sign_of_entering_delta = this->m_d[entering] > 0? 1 : -1;
        if (this->m_using_infeas_costs && this->m_settings.use_breakpoints_in_feasibility_search)
            m_sign_of_entering_delta = - m_sign_of_entering_delta;
        m_non_basis_list.erase(entering_iter);
        m_non_basis_list.push_back(entering);
        return entering;
    }
    return -1;
}

template <typename T, typename X> int lp_primal_core_solver<T, X>::advance_on_sorted_breakpoints(unsigned entering, X &t) {
    T slope_at_entering = this->m_d[entering];
    breakpoint<X> * last_bp = nullptr;
    lp_assert(m_breakpoint_indices_queue.is_empty()==false);
    while (m_breakpoint_indices_queue.is_empty() == false) {
        unsigned bi = m_breakpoint_indices_queue.dequeue();
        breakpoint<X> *b = &m_breakpoints[bi];
        change_slope_on_breakpoint(entering, b, slope_at_entering);
        last_bp = b;
        if (slope_at_entering * m_sign_of_entering_delta > - m_epsilon_of_reduced_cost) { // the slope started to increase infeasibility
            break;
        } else {
            if ((numeric_traits<T>::precise() == false) || ( numeric_traits<T>::is_zero(slope_at_entering) && this->m_settings.random_next() % 2 == 0)) {
                // it is not cost beneficial to advance the delta more, so just break to increase the randomness
                break;
            }
        }        
    }
    lp_assert (last_bp != nullptr);
    t = last_bp->m_delta;
    return last_bp->m_j;
}


template <typename T, typename X> int
lp_primal_core_solver<T, X>::find_leaving_and_t_with_breakpoints(unsigned entering, X & t){
    lp_assert(this->precise() == false);
    fill_breakpoints_array(entering);
    return advance_on_sorted_breakpoints(entering, t);
}

template <typename T, typename X> bool lp_primal_core_solver<T, X>::get_harris_theta(X & theta) {
    lp_assert(this->m_ed.is_OK());
    bool unlimited = true;
    for (unsigned i : this->m_ed.m_index) {
        if (this->m_settings.abs_val_is_smaller_than_pivot_tolerance(this->m_ed[i])) continue;
        limit_theta_on_basis_column(this->m_basis[i], - this->m_ed[i] * m_sign_of_entering_delta, theta, unlimited);
        if (!unlimited && is_zero<X>(theta)) break;
    }
    return unlimited;
}


template <typename T, typename X> int lp_primal_core_solver<T, X>::
find_leaving_on_harris_theta(X const & harris_theta, X & t) {
    int leaving = -1;
    T pivot_abs_max = zero_of_type<T>();
    // we know already that there is no bound flip on entering
    // we also know that harris_theta is limited, so we will find a leaving
    zero_harris_eps();
    unsigned steps = this->m_ed.m_index.size();
    unsigned k = this->m_settings.random_next() % steps;
    unsigned initial_k = k;
    do {
        unsigned i = this->m_ed.m_index[k];
        const T & ed = this->m_ed[i];
        if (this->m_settings.abs_val_is_smaller_than_pivot_tolerance(ed)) {
            if (++k == steps)
                k = 0;
            continue;
        }
        X ratio;
        unsigned j = this->m_basis[i];
        bool unlimited = true;
        limit_theta_on_basis_column(j, - ed * m_sign_of_entering_delta, ratio, unlimited);
        if ((!unlimited) && ratio <= harris_theta) {
            if (leaving == -1 || abs(ed) > pivot_abs_max) {
                t = ratio;
                leaving = j;
                pivot_abs_max = abs(ed);
            }
        }
        if (++k == steps) k = 0;
    } while (k != initial_k);
    if (!this->precise())
        restore_harris_eps();
    return leaving;
}


template <typename T, typename X> bool lp_primal_core_solver<T, X>::try_jump_to_another_bound_on_entering(unsigned entering,
                                                                                                          const X & theta,
                                                                                                          X & t,
                                                                                                          bool & unlimited) {
    switch(this->m_column_types[entering]){
    case column_type::boxed: 
        if (m_sign_of_entering_delta > 0) {
            t = this->m_upper_bounds[entering] - this->m_x[entering];
            if (unlimited || t <= theta){
                lp_assert(t >= zero_of_type<X>());
                return true;
            }
        } else { // m_sign_of_entering_delta == -1
            t = this->m_x[entering] - this->m_lower_bounds[entering];
            if (unlimited || t <= theta) {
                lp_assert(t >= zero_of_type<X>());
                return true;
            }
        }
        return false;
    case column_type::upper_bound:
        if (m_sign_of_entering_delta > 0) {
            t = this->m_upper_bounds[entering] - this->m_x[entering];
            if (unlimited || t <= theta){
                lp_assert(t >= zero_of_type<X>());
                return true;
            }
        }
        return false;
    case column_type::lower_bound:
        if (m_sign_of_entering_delta < 0) {
                t = this->m_x[entering] - this->m_lower_bounds[entering];
                if (unlimited || t <= theta) {
                    lp_assert(t >= zero_of_type<X>());
                    return true;
                }
        }
        return false;
    default:return false;
    }
    return false;
}

template <typename T, typename X> bool lp_primal_core_solver<T, X>::
try_jump_to_another_bound_on_entering_unlimited(unsigned entering, X & t ) {
    if (this->m_column_types[entering] != column_type::boxed)
        return false;

    if (m_sign_of_entering_delta > 0) {
        t = this->m_upper_bounds[entering] - this->m_x[entering];
        return true;
    }
     // m_sign_of_entering_delta == -1
    t = this->m_x[entering] - this->m_lower_bounds[entering];
    return true;
}

template <typename T, typename X> int lp_primal_core_solver<T, X>::find_leaving_and_t_precise(unsigned entering, X & t) {
    if (this->m_settings.use_breakpoints_in_feasibility_search && !this->current_x_is_feasible())
        return find_leaving_and_t_with_breakpoints(entering, t);
    bool unlimited = true;
    unsigned steps = this->m_ed.m_index.size();
    unsigned k = this->m_settings.random_next() % steps;
    unsigned initial_k = k;
    unsigned row_min_nz = this->m_n() + 1;
    m_leaving_candidates.clear();
    do {
        unsigned i = this->m_ed.m_index[k];
        const T & ed = this->m_ed[i];
        lp_assert(!numeric_traits<T>::is_zero(ed));
        unsigned j = this->m_basis[i];
        limit_theta_on_basis_column(j, - ed * m_sign_of_entering_delta, t, unlimited);
        if (!unlimited) {
            m_leaving_candidates.push_back(j);
            row_min_nz = this->m_rows_nz[i];
        }
        if (++k == steps) k = 0;
    } while (unlimited && k != initial_k);
    if (unlimited) {
        if (try_jump_to_another_bound_on_entering_unlimited(entering, t))
            return entering;
        return -1;
    }

    X ratio;
    while (k != initial_k) {
        unsigned i = this->m_ed.m_index[k];
        const T & ed = this->m_ed[i];
        lp_assert(!numeric_traits<T>::is_zero(ed));
        unsigned j = this->m_basis[i];
        unlimited = true;
        limit_theta_on_basis_column(j, -ed * m_sign_of_entering_delta, ratio, unlimited);
        if (unlimited) {
            if (++k == steps) k = 0;
            continue;
        }
        unsigned i_nz = this->m_rows_nz[i];
        if (ratio < t) {
            t = ratio;
            m_leaving_candidates.clear();
            m_leaving_candidates.push_back(j);
            row_min_nz = this->m_rows_nz[i];
        } else if (ratio == t && i_nz < row_min_nz) {
            m_leaving_candidates.clear();
            m_leaving_candidates.push_back(j);
            row_min_nz = this->m_rows_nz[i];
        } else if (ratio == t && i_nz == row_min_nz) {
            m_leaving_candidates.push_back(j);
        }
        if (++k == steps) k = 0;
    }

    ratio = t;
    unlimited = false;
    if (try_jump_to_another_bound_on_entering(entering, t, ratio, unlimited)) {
        t = ratio;
        return entering;
    }
    k = this->m_settings.random_next() % m_leaving_candidates.size();
    return m_leaving_candidates[k];
}


template <typename T, typename X>    int lp_primal_core_solver<T, X>::find_leaving_and_t(unsigned entering, X & t) {
    if (this->m_settings.use_breakpoints_in_feasibility_search && !this->current_x_is_feasible())
        return find_leaving_and_t_with_breakpoints(entering, t);
    X theta;
    bool unlimited = get_harris_theta(theta);
    lp_assert(unlimited || theta >= zero_of_type<X>());
    if (try_jump_to_another_bound_on_entering(entering, theta, t, unlimited)) return entering;
    if (unlimited)
        return -1;
    return find_leaving_on_harris_theta(theta, t);
}



// m is the multiplier. updating t in a way that holds the following
// x[j] + t * m >= m_lower_bounds[j] ( if m < 0 )
// or
// x[j] + t * m <= this->m_upper_bounds[j] ( if m > 0)
template <typename T, typename X> void
lp_primal_core_solver<T, X>::get_bound_on_variable_and_update_leaving_precisely(unsigned j, vector<unsigned> & leavings, T m, X & t, T & abs_of_d_of_leaving) {
    if (m > 0) {
        switch(this->m_column_types[j]) { // check that j has a low bound
        case column_type::free_column:
        case column_type::upper_bound:
            return;
        default:break;
        }
        X tt = - (this->m_lower_bounds[j] - this->m_x[j]) / m;
        if (numeric_traits<X>::is_neg(tt))
            tt = zero_of_type<X>();
        if (leavings.empty() || tt < t || (tt == t && m > abs_of_d_of_leaving)) {
            t = tt;
            abs_of_d_of_leaving = m;
            leavings.clear();
            leavings.push_back(j);
        }
        else if (tt == t || m == abs_of_d_of_leaving) {
            leavings.push_back(j);
        }
    } else if (m < 0){
        switch (this->m_column_types[j]) { // check that j has an upper bound
        case column_type::free_column:
        case column_type::lower_bound:
            return;
        default:break;
        }

        X tt = (this->m_upper_bounds[j] - this->m_x[j]) / m;
        if (numeric_traits<X>::is_neg(tt))
            tt = zero_of_type<X>();
        if (leavings.empty() || tt < t || (tt == t && - m > abs_of_d_of_leaving)) {
            t = tt;
            abs_of_d_of_leaving = - m;
            leavings.clear();
            leavings.push_back(j);
        } else if (tt == t || m == abs_of_d_of_leaving) {
            leavings.push_back(j);
        }
    }
}

template <typename T, typename X>    X lp_primal_core_solver<T, X>::get_max_bound(vector<X> & b) {
    X ret = zero_of_type<X>();
    for (auto & v : b) {
        X a = abs(v);
        if (a > ret) ret = a;
    }
    return ret;
}

#ifdef Z3DEBUG
template <typename T, typename X>   void lp_primal_core_solver<T, X>::check_Ax_equal_b() {
    dense_matrix<T, X> d(this->m_A);
    T * ls = d.apply_from_left_with_different_dims(this->m_x);
    lp_assert(vectors_are_equal<T>(ls, this->m_b, this->m_m()));
    delete [] ls;
}
template <typename T, typename X>    void lp_primal_core_solver<T, X>::check_the_bounds() {
    for (unsigned i = 0; i < this->m_n(); i++) {
        check_bound(i);
    }
}

template <typename T, typename X>    void lp_primal_core_solver<T, X>::check_bound(unsigned i) {
    lp_assert (!(this->column_has_lower_bound(i) && (numeric_traits<T>::zero() > this->m_x[i])));
    lp_assert (!(this->column_has_upper_bound(i) && (this->m_upper_bounds[i] < this->m_x[i])));
}

template <typename T, typename X>    void lp_primal_core_solver<T, X>::check_correctness() {
    check_the_bounds();
    check_Ax_equal_b();
}
#endif

// from page 183 of Istvan Maros's book
// the basis structures have not changed yet
template <typename T, typename X>
void lp_primal_core_solver<T, X>::update_reduced_costs_from_pivot_row(unsigned entering, unsigned leaving) {
    // the basis heading has changed already
#ifdef Z3DEBUG
    auto & basis_heading = this->m_basis_heading;
    lp_assert(basis_heading[entering] >= 0 && static_cast<unsigned>(basis_heading[entering]) < this->m_m());
    lp_assert(basis_heading[leaving] < 0);
#endif
    T pivot = this->m_pivot_row[entering];
    T dq = this->m_d[entering]/pivot;
    for (auto j : this->m_pivot_row.m_index) {
        //            for (auto j : this->m_nbasis)
        if (this->m_basis_heading[j] >= 0) continue;
        if (j != leaving)
            this->m_d[j] -= dq * this->m_pivot_row[j];
    }
    this->m_d[leaving] = -dq;
    if (this->current_x_is_infeasible() && !this->m_settings.use_breakpoints_in_feasibility_search) {
        this->m_d[leaving] -= this->m_costs[leaving];
        this->m_costs[leaving] = zero_of_type<T>();
    }
    this->m_d[entering] = numeric_traits<T>::zero();
}

// return 0 if the reduced cost at entering is close enough to the refreshed
// 1 if it is way off, and 2 if it is unprofitable
template <typename T, typename X>    int lp_primal_core_solver<T, X>::refresh_reduced_cost_at_entering_and_check_that_it_is_off(unsigned entering) {
    if (numeric_traits<T>::precise()) return 0;
    T reduced_at_entering_was = this->m_d[entering];  // can benefit from going over non-zeros of m_ed
    lp_assert(abs(reduced_at_entering_was) > m_epsilon_of_reduced_cost);
    T refreshed_cost = this->m_costs[entering];
    unsigned i = this->m_m();
    while (i--) refreshed_cost -= this->m_costs[this->m_basis[i]] * this->m_ed[i];
    this->m_d[entering] = refreshed_cost;
    T delta = abs(reduced_at_entering_was - refreshed_cost);
    if (delta * 2 > abs(reduced_at_entering_was)) {
        // this->m_status = UNSTABLE;
        if (reduced_at_entering_was > m_epsilon_of_reduced_cost) {
            if (refreshed_cost <= zero_of_type<T>())
                return 2; // abort entering
        } else {
            if (refreshed_cost > -m_epsilon_of_reduced_cost)
                return 2; // abort entering
        }
        return 1; // go on with this entering
    } else {
        if (reduced_at_entering_was > m_epsilon_of_reduced_cost) {
            if (refreshed_cost <= zero_of_type<T>())
                return 2; // abort entering
        } else {
            if (refreshed_cost > -m_epsilon_of_reduced_cost)
                return 2; // abort entering
        }
    }
    return 0;
}

template <typename T, typename X>    void lp_primal_core_solver<T, X>::backup_and_normalize_costs() {
    if (this->m_look_for_feasible_solution_only)
        return; // no need to backup cost, since we are going to use only feasibility costs
    if (numeric_traits<T>::precise() ) {        
        m_costs_backup = this->m_costs;
    } else {
        T cost_max = std::max(max_abs_in_vector(this->m_costs), T(1));
        lp_assert(m_costs_backup.size() == 0);
        for (unsigned j = 0; j < this->m_costs.size(); j++)
            m_costs_backup.push_back(this->m_costs[j] /= cost_max);
    }
}

template <typename T, typename X>    void lp_primal_core_solver<T, X>::init_run() {
    this->m_basis_sort_counter = 0; // to initiate the sort of the basis
    this->set_total_iterations(0);
    this->iters_with_no_cost_growing() = 0;
    init_inf_set();
    if (this->current_x_is_feasible() && this->m_look_for_feasible_solution_only)
        return;
    this->m_using_infeas_costs = false;
    if (this->m_settings.backup_costs)
        backup_and_normalize_costs();
    m_epsilon_of_reduced_cost = numeric_traits<X>::precise()? zero_of_type<T>(): T(1)/T(10000000);
    m_breakpoint_indices_queue.resize(this->m_n());
    init_reduced_costs();
    if (!numeric_traits<X>::precise()) {
        this->m_column_norm_update_counter = 0;
        init_column_norms();
    } else {
        if (this->m_columns_nz.size() != this->m_n())
            init_column_row_non_zeroes();
    }
}


template <typename T, typename X>    void lp_primal_core_solver<T, X>::calc_working_vector_beta_for_column_norms(){
    lp_assert(numeric_traits<T>::precise() == false);
    lp_assert(this->m_ed.is_OK());
    lp_assert(m_beta.is_OK());
    m_beta = this->m_ed;
    this->m_factorization->solve_yB_with_error_check_indexed(m_beta, this->m_basis_heading, this->m_basis, this->m_settings);
}

template <typename T, typename X>
void lp_primal_core_solver<T, X>::advance_on_entering_equal_leaving(int entering, X & t) {
    CASSERT("A_off", !this->A_mult_x_is_off() );
    this->update_x(entering, t * m_sign_of_entering_delta);
    if (this->A_mult_x_is_off_on_index(this->m_ed.m_index) && !this->find_x_by_solving()) {
        this->init_lu();
        if (!this->find_x_by_solving()) {
            this->restore_x(entering, t * m_sign_of_entering_delta);
            this->iters_with_no_cost_growing()++;
            LP_OUT(this->m_settings, "failing in advance_on_entering_equal_leaving for entering = " << entering << std::endl);
            return;
        }
    }
    if (this->m_using_infeas_costs) {
        lp_assert(is_zero(this->m_costs[entering])); 
        init_infeasibility_costs_for_changed_basis_only();
    }
    if (this->m_look_for_feasible_solution_only && this->current_x_is_feasible())
        return;
    
    if (need_to_switch_costs() ||!this->current_x_is_feasible()) {
        init_reduced_costs();
    }
    this->iters_with_no_cost_growing() = 0;
}

template <typename T, typename X>void lp_primal_core_solver<T, X>::advance_on_entering_and_leaving(int entering, int leaving, X & t) {
    lp_assert(entering >= 0 && m_non_basis_list.back() == static_cast<unsigned>(entering));
    lp_assert(this->m_using_infeas_costs || t >= zero_of_type<X>());
    lp_assert(leaving >= 0 && entering >= 0);
    lp_assert(entering != leaving || !is_zero(t)); // otherwise nothing changes
    if (entering == leaving) {
        advance_on_entering_equal_leaving(entering, t);
        return;
    }
    unsigned pivot_row = this->m_basis_heading[leaving];
    this->calculate_pivot_row_of_B_1(pivot_row);
    this->calculate_pivot_row_when_pivot_row_of_B1_is_ready(pivot_row);

    int pivot_compare_result = this->pivots_in_column_and_row_are_different(entering, leaving);
    if (!pivot_compare_result){;}
    else if (pivot_compare_result == 2) { // the sign is changed, cannot continue
        this->set_status(lp_status::UNSTABLE);
        this->iters_with_no_cost_growing()++;
        return;
    } else {
        lp_assert(pivot_compare_result == 1);
        this->init_lu();
        if (this->m_factorization == nullptr || this->m_factorization->get_status() != LU_status::OK) {
            this->set_status(lp_status::UNSTABLE);
            this->iters_with_no_cost_growing()++;
            return;
        }
    }
    if (!numeric_traits<T>::precise())
        calc_working_vector_beta_for_column_norms();
    if (this->current_x_is_feasible() || !this->m_settings.use_breakpoints_in_feasibility_search) {
        if (m_sign_of_entering_delta == -1)
            t = -t;
    }
    if (!this->update_basis_and_x(entering, leaving, t)) {
        if (this->get_status() == lp_status::FLOATING_POINT_ERROR)
            return;
        if (this->m_look_for_feasible_solution_only) {
            this->set_status(lp_status::FLOATING_POINT_ERROR);
            return;
        }
        init_reduced_costs();
        return;
    }

    if (!is_zero(t)) {
        this->iters_with_no_cost_growing() = 0;
        init_infeasibility_after_update_x_if_inf(leaving);
    }

    if (this->current_x_is_feasible()) {
        this->set_status(lp_status::FEASIBLE);
        if (this->m_look_for_feasible_solution_only)
            return;
    }
    if (numeric_traits<X>::precise() == false)
        update_or_init_column_norms(entering, leaving);

    
    if (need_to_switch_costs()) {
        init_reduced_costs();
    }  else {
        update_reduced_costs_from_pivot_row(entering, leaving);
    }
    lp_assert(!need_to_switch_costs());
    std::list<unsigned>::iterator it = m_non_basis_list.end();
    it--;
    * it = static_cast<unsigned>(leaving);
}


template <typename T, typename X> void lp_primal_core_solver<T, X>::advance_on_entering_precise(int entering) {
    lp_assert(numeric_traits<T>::precise());
    lp_assert(entering > -1);
    this->solve_Bd(entering);
    X t;
    int leaving = find_leaving_and_t_precise(entering, t);
    if (leaving == -1) {
        TRACE("lar_solver", tout << "non-leaving\n";);
        this->set_status(lp_status::UNBOUNDED);
        return;
    }
    advance_on_entering_and_leaving(entering, leaving, t);
}

template <typename T, typename X> void lp_primal_core_solver<T, X>::advance_on_entering(int entering) {
    if (numeric_traits<T>::precise()) {
        advance_on_entering_precise(entering);
        return;
    }
    lp_assert(entering > -1);
    this->solve_Bd(entering);
    int refresh_result = refresh_reduced_cost_at_entering_and_check_that_it_is_off(entering);
    if (refresh_result) {
        if (this->m_look_for_feasible_solution_only) {
            this->set_status(lp_status::FLOATING_POINT_ERROR);
            return;
        }

        this->init_lu();
        init_reduced_costs();
        if (refresh_result == 2) {
            this->iters_with_no_cost_growing()++;
            return;
        }
    }
    X t;
    int leaving = find_leaving_and_t(entering, t);
    if (leaving == -1){
        if (!this->current_x_is_feasible()) {
            lp_assert(!numeric_traits<T>::precise()); // we cannot have unbounded with inf costs
               
            // if (m_look_for_feasible_solution_only) {
            //     this->m_status = INFEASIBLE;
            //     return;
            //  }
            
                
            if (this->get_status() == lp_status::UNSTABLE) {
                this->set_status(lp_status::FLOATING_POINT_ERROR);
                return;
            }
            init_infeasibility_costs();
            this->set_status(lp_status::UNSTABLE);

            return;
        }
        if (this->get_status() == lp_status::TENTATIVE_UNBOUNDED) {
            this->set_status(lp_status::UNBOUNDED);
        } else {
            this->set_status(lp_status::TENTATIVE_UNBOUNDED);
        }
        TRACE("lar_solver", tout << this->get_status() << "\n";);
        return;
    }
    advance_on_entering_and_leaving(entering, leaving, t);
}

template <typename T, typename X>    void lp_primal_core_solver<T, X>::push_forward_offset_in_non_basis(unsigned & offset_in_nb) {
    if (++offset_in_nb == this->m_nbasis.size())
        offset_in_nb = 0;
}

template <typename T, typename X>  unsigned lp_primal_core_solver<T, X>::get_number_of_non_basic_column_to_try_for_enter() {
    unsigned ret = static_cast<unsigned>(this->m_nbasis.size());
    if (this->get_status() == lp_status::TENTATIVE_UNBOUNDED)
        return ret; // we really need to find entering with a large reduced cost
    if (ret > 300) {
        ret = (unsigned)(ret * this->m_settings.percent_of_entering_to_check / 100);
    }
    if (ret == 0) {
        return 0;
    }
    return std::max(static_cast<unsigned>(this->m_settings.random_next() % ret), 1u);
}

template <typename T, typename X> void lp_primal_core_solver<T, X>::print_column_norms(std::ostream & out) {
    out << " column norms " << std::endl;
    for (unsigned j = 0; j < this->m_n(); j++) {
        out << this->m_column_norms[j] << " ";
    }
    out << std::endl;
 }

// returns the number of iterations
template <typename T, typename X> unsigned lp_primal_core_solver<T, X>::solve() {
    TRACE("lar_solver", tout << "solve " << this->get_status() << "\n";);
    if (numeric_traits<T>::precise() && this->m_settings.use_tableau())
        return solve_with_tableau();

    init_run();
    if (this->current_x_is_feasible() && this->m_look_for_feasible_solution_only) {
        this->set_status(lp_status::FEASIBLE);
        return 0;
    }
        
    if ((!numeric_traits<T>::precise()) && this->A_mult_x_is_off()) {
        this->set_status(lp_status::FLOATING_POINT_ERROR);
        return 0;
    }
    do {
        if (this->print_statistics_with_iterations_and_nonzeroes_and_cost_and_check_that_the_time_is_over((this->m_using_infeas_costs? "inf" : "feas"), * this->m_settings.get_message_ostream())) {
            return this->total_iterations();
        }
        one_iteration();

        TRACE("lar_solver", tout << "one iteration: " << this->get_status() << "\n";);
        lp_assert(!this->m_using_infeas_costs || this->costs_on_nbasis_are_zeros());
        switch (this->get_status()) {
        case lp_status::OPTIMAL:  // double check that we are at optimum
        case lp_status::INFEASIBLE:
            if (this->m_look_for_feasible_solution_only && this->current_x_is_feasible())
                break;
            if (!numeric_traits<T>::precise()) {
                if(this->m_look_for_feasible_solution_only)
                    break;
                this->init_lu();
                
                if (this->m_factorization->get_status() != LU_status::OK) {
                    this->set_status (lp_status::FLOATING_POINT_ERROR);
                    break;
                }
                init_reduced_costs();
                if (choose_entering_column(1) == -1) {
                    decide_on_status_when_cannot_find_entering();
                    break;
                }
                this->set_status(lp_status::UNKNOWN);
            } else { // precise case
                if (this->m_look_for_feasible_solution_only) { // todo: keep the reduced costs correct all the time!
                    init_reduced_costs();
                    if (choose_entering_column(1) == -1) {
                        decide_on_status_when_cannot_find_entering();
                        break;
                    }
                    this->set_status(lp_status::UNKNOWN);
                }
            }
            break;
        case lp_status::TENTATIVE_UNBOUNDED:
            this->init_lu();
            if (this->m_factorization->get_status() != LU_status::OK) {
                this->set_status(lp_status::FLOATING_POINT_ERROR);
                break;
            }
                
            init_reduced_costs();
            break;
        case lp_status::UNBOUNDED:
            if (this->current_x_is_infeasible()) {
                init_reduced_costs();
                this->set_status(lp_status::UNKNOWN);
            }
            break;

        case lp_status::UNSTABLE:
            lp_assert(! (numeric_traits<T>::precise()));
            this->init_lu();
            if (this->m_factorization->get_status() != LU_status::OK) {
                this->set_status(lp_status::FLOATING_POINT_ERROR);
                break;
            }
            init_reduced_costs();
            break;

        default:
            break; // do nothing
        }
    } while (this->get_status() != lp_status::FLOATING_POINT_ERROR
             &&
             this->get_status() != lp_status::UNBOUNDED
             &&
             this->get_status() != lp_status::OPTIMAL
             &&
             this->get_status() != lp_status::INFEASIBLE
             &&
             this->iters_with_no_cost_growing() <= this->m_settings.max_number_of_iterations_with_no_improvements
             &&
             this->total_iterations() <= this->m_settings.max_total_number_of_iterations
             &&
             !(this->current_x_is_feasible() && this->m_look_for_feasible_solution_only));

    lp_assert(this->get_status() == lp_status::FLOATING_POINT_ERROR
                ||
                this->current_x_is_feasible() == false
                ||
                this->calc_current_x_is_feasible_include_non_basis());
    return this->total_iterations();
}

template <typename T, typename X>    void lp_primal_core_solver<T, X>::delete_factorization() {
    if (this->m_factorization != nullptr) {
        delete this->m_factorization;
        this->m_factorization = nullptr;
    }
}

// according to Swietanowski, " A new steepest edge approximation for the simplex method for linear programming"
template <typename T, typename X> void lp_primal_core_solver<T, X>::init_column_norms() {
    lp_assert(numeric_traits<T>::precise() == false);
    for (unsigned j = 0; j < this->m_n(); j++) {
        this->m_column_norms[j] = T(static_cast<int>(this->m_A.m_columns[j].size() + 1)) 
            
            + T(static_cast<int>(this->m_settings.random_next() % 10000)) / T(100000);
    }
}

// debug only
template <typename T, typename X> T lp_primal_core_solver<T, X>::calculate_column_norm_exactly(unsigned j) {
    lp_assert(numeric_traits<T>::precise() == false);
    indexed_vector<T> w(this->m_m());
    this->m_A.copy_column_to_vector(j, w);
    vector<T> d(this->m_m());
    this->m_factorization->solve_Bd_when_w_is_ready(d, w);
    T ret = zero_of_type<T>();
    for (auto v : d)
        ret += v*v;
    return ret+1;
}

template <typename T, typename X>    void lp_primal_core_solver<T, X>::update_or_init_column_norms(unsigned entering, unsigned leaving) {
    lp_assert(numeric_traits<T>::precise() == false);
    lp_assert(m_column_norm_update_counter <= this->m_settings.column_norms_update_frequency);
    if (m_column_norm_update_counter == this->m_settings.column_norms_update_frequency) {
        m_column_norm_update_counter = 0;
        init_column_norms();
    } else {
        m_column_norm_update_counter++;
        update_column_norms(entering, leaving);
    }
}

// following Swietanowski - A new steepest ...
template <typename T, typename X>    void lp_primal_core_solver<T, X>::update_column_norms(unsigned entering, unsigned leaving) {
    lp_assert(numeric_traits<T>::precise() == false);
    T pivot = this->m_pivot_row[entering];
    T g_ent = calculate_norm_of_entering_exactly() / pivot / pivot;
    if (!numeric_traits<T>::precise()) {
        if (g_ent < T(0.000001))
            g_ent = T(0.000001);
    }
    this->m_column_norms[leaving] = g_ent;

    for (unsigned j : this->m_pivot_row.m_index) {
        if (j == leaving)
            continue;
        const T & t = this->m_pivot_row[j];
        T s = this->m_A.dot_product_with_column(m_beta.m_data, j);
        T k = -2 / pivot;
        T tp = t/pivot;
        if (this->m_column_types[j] != column_type::fixed) { // a fixed columns do not enter the basis, we don't use the norm of a fixed column
            this->m_column_norms[j] = std::max(this->m_column_norms[j] + t * (t * g_ent + k * s), // see Istvan Maros, page 196
                                               1 + tp * tp);
             }
    }
}

template <typename T, typename X>    T lp_primal_core_solver<T, X>::calculate_norm_of_entering_exactly() {
    T r = numeric_traits<T>::one();
    for (auto i : this->m_ed.m_index) {
        T t = this->m_ed[i];
        r += t * t;
    }
    return r;
}

// calling it stage1 is too cryptic
template <typename T, typename X>    void lp_primal_core_solver<T, X>::find_feasible_solution() {
    this->m_look_for_feasible_solution_only = true;
    lp_assert(this->non_basic_columns_are_set_correctly());
    this->set_status(lp_status::UNKNOWN);
    solve();
}

template <typename T, typename X> void lp_primal_core_solver<T, X>::one_iteration() {
    unsigned number_of_benefitial_columns_to_go_over = get_number_of_non_basic_column_to_try_for_enter();
    int entering = choose_entering_column(number_of_benefitial_columns_to_go_over);
    if (entering == -1) {
        decide_on_status_when_cannot_find_entering();
    }
    else {
        advance_on_entering(entering);
    }
}

template <typename T, typename X>    void lp_primal_core_solver<T, X>::update_basis_and_x_with_comparison(unsigned entering, unsigned leaving, X delta) {
    if (entering != leaving)
        this->update_basis_and_x(entering, leaving, delta);
    else
        this->update_x(entering, delta);
}


template <typename T, typename X> void lp_primal_core_solver<T, X>::clear_breakpoints() {
    m_breakpoints.clear();
    m_breakpoint_indices_queue.clear();
}

template <typename T, typename X> void lp_primal_core_solver<T, X>::fill_breakpoints_array(unsigned entering) {
    clear_breakpoints();
    for (unsigned i : this->m_ed.m_index)
        try_add_breakpoint_in_row(i);

    if (this->m_column_types[entering] == column_type::boxed) {
        if (m_sign_of_entering_delta < 0)
            add_breakpoint(entering, - this->bound_span(entering), low_break);
        else
            add_breakpoint(entering, this->bound_span(entering), upper_break);
    }
}



template <typename T, typename X> bool lp_primal_core_solver<T, X>::done() {
    if (this->get_status() == lp_status::OPTIMAL || this->get_status() == lp_status::FLOATING_POINT_ERROR) return true;
    if (this->get_status() == lp_status::INFEASIBLE) {
        return true;
    }
    if (this->m_iters_with_no_cost_growing >= this->m_settings.max_number_of_iterations_with_no_improvements) {
        this->get_status() = lp_status::ITERATIONS_EXHAUSTED; return true;
    }
    if (this->total_iterations() >= this->m_settings.max_total_number_of_iterations) {
        this->get_status() = lp_status::ITERATIONS_EXHAUSTED; return true;
    }
    return false;
}

template <typename T, typename X>
void lp_primal_core_solver<T, X>::init_infeasibility_costs_for_changed_basis_only() {
    for (unsigned i :  this->m_ed.m_index)
        init_infeasibility_cost_for_column(this->m_basis[i]);
    this->m_using_infeas_costs = true;
}


template <typename T, typename X>
void lp_primal_core_solver<T, X>::init_infeasibility_costs() {
    lp_assert(this->m_x.size() >= this->m_n());
    lp_assert(this->m_column_types.size() >= this->m_n());
    for (unsigned j = this->m_n(); j--;)
        init_infeasibility_cost_for_column(j);
    this->m_using_infeas_costs = true;
}

template <typename T, typename X> T
lp_primal_core_solver<T, X>::get_infeasibility_cost_for_column(unsigned j) const {
    if (this->m_basis_heading[j] < 0) {
        return zero_of_type<T>();
    }
    T ret;
    // j is a basis column
    switch (this->m_column_types[j]) {
    case column_type::fixed:
    case column_type::boxed:
        if (this->x_above_upper_bound(j)) {
            ret = 1;
        } else if (this->x_below_low_bound(j)) {
            ret = -1;
        } else {
            ret = numeric_traits<T>::zero();
        }
        break;
    case column_type::lower_bound:
        if (this->x_below_low_bound(j)) {
            ret = -1;
        } else {
            ret = numeric_traits<T>::zero();
        }
        break;
    case column_type::upper_bound:
        if (this->x_above_upper_bound(j)) {
            ret = 1;
        } else {
            ret = numeric_traits<T>::zero();
        }
        break;
    case column_type::free_column:
        ret = numeric_traits<T>::zero();
        break;
    default:
        lp_assert(false);
        ret = numeric_traits<T>::zero(); // does not matter
        break;
    }
    
    if (!this->m_settings.use_breakpoints_in_feasibility_search) {
        ret = - ret;
    }
    return ret;
}


// changed m_inf_set too!
template <typename T, typename X> void
lp_primal_core_solver<T, X>::init_infeasibility_cost_for_column(unsigned j) {

    // If j is a breakpoint column, then we set the cost zero.
    // When anylyzing an entering column candidate we update the cost of the breakpoints columns to get the left or the right derivative if the infeasibility function
    // set zero cost for each non-basis column
    if (this->m_basis_heading[j] < 0) {
        this->m_costs[j] = numeric_traits<T>::zero();
        this->m_inf_set.erase(j);
        return;
    }
    // j is a basis column
    switch (this->m_column_types[j]) {
    case column_type::fixed:
    case column_type::boxed:
        if (this->x_above_upper_bound(j)) {
            this->m_costs[j] = 1;
        } else if (this->x_below_low_bound(j)) {
            this->m_costs[j] = -1;
        } else {
            this->m_costs[j] = numeric_traits<T>::zero();
        }
        break;
    case column_type::lower_bound:
        if (this->x_below_low_bound(j)) {
            this->m_costs[j] = -1;
        } else {
            this->m_costs[j] = numeric_traits<T>::zero();
        }
        break;
    case column_type::upper_bound:
        if (this->x_above_upper_bound(j)) {
            this->m_costs[j] = 1;
        } else {
            this->m_costs[j] = numeric_traits<T>::zero();
        }
        break;
    case column_type::free_column:
        this->m_costs[j] = numeric_traits<T>::zero();
        break;
    default:
        lp_assert(false);
        break;
    }
    
    if (numeric_traits<T>::is_zero(this->m_costs[j])) {
        this->remove_column_from_inf_set(j);
    } else {
        this->insert_column_into_inf_set(j);
    }
    if (!this->m_settings.use_breakpoints_in_feasibility_search) {
        this->m_costs[j] = - this->m_costs[j];
    }
}


template <typename T, typename X> void lp_primal_core_solver<T, X>::print_column(unsigned j, std::ostream & out) {
    out << this->column_name(j) << " " <<   j << " " << column_type_to_string(this->m_column_type[j]) << " x = " << this->m_x[j] << " " << "c = " << this->m_costs[j];;
    switch (this->m_column_type[j]) {
    case column_type::fixed:
    case column_type::boxed:
        out <<  "( " << this->m_lower_bounds[j] << " " << this->m_x[j] << " " << this->m_upper_bounds[j] << ")" << std::endl;
        break;
    case column_type::upper_bound:
        out <<  "( _"  << this->m_x[j] << " " << this->m_upper_bounds[j] << ")" << std::endl;
        break;
    case column_type::lower_bound:
        out <<  "( " << this->m_lower_bounds[j] << " " << this->m_x[j] << " " << "_ )" << std::endl;
        break;
    case column_type::free_column:
        out << "( _" << this->m_x[j] << "_)" << std::endl;
        break;
    default:
        lp_unreachable();
    }
}

template <typename T, typename X>    void lp_primal_core_solver<T, X>::add_breakpoint(unsigned j, X delta, breakpoint_type type) {
    m_breakpoints.push_back(breakpoint<X>(j, delta, type));
    m_breakpoint_indices_queue.enqueue(m_breakpoint_indices_queue.size(), abs(delta));
}

// j is the basic column, x is the value at x[j]
// d is the coefficient before m_entering in the row with j as the basis column
template <typename T, typename X>    void lp_primal_core_solver<T, X>::try_add_breakpoint(unsigned j, const X & x, const T & d, breakpoint_type break_type, const X & break_value) {
    X diff = x - break_value;
    if (is_zero(diff)) {
        switch (break_type) {
        case low_break:
            if (!same_sign_with_entering_delta(d))
                return; // no breakpoint
            break;
        case upper_break:
            if (same_sign_with_entering_delta(d))
                return; // no breakpoint
            break;
        default: break;
        }
        add_breakpoint(j, zero_of_type<X>(), break_type);
        return;
    }
    auto delta_j =  diff / d;
    if (same_sign_with_entering_delta(delta_j))
        add_breakpoint(j, delta_j, break_type);
}

template <typename T, typename X> std::string lp_primal_core_solver<T, X>::break_type_to_string(breakpoint_type type) {
    switch (type){
    case low_break: return "low_break";
    case upper_break: return "upper_break";
    case fixed_break: return "fixed_break";
    default:
        lp_assert(false);
        break;
    }
    return "type is not found";
}

template <typename T, typename X> void lp_primal_core_solver<T, X>::print_breakpoint(const breakpoint<X> * b, std::ostream & out) {
    out << "(" << this->column_name(b->m_j) << "," << break_type_to_string(b->m_type) << "," << T_to_string(b->m_delta) << ")" << std::endl;
    print_bound_info_and_x(b->m_j, out);
}

template <typename T, typename X>
void lp_primal_core_solver<T, X>::init_reduced_costs() {
    lp_assert(!this->use_tableau());
    if (this->current_x_is_infeasible() && !this->m_using_infeas_costs) {
        init_infeasibility_costs();
    } else if (this->current_x_is_feasible() && this->m_using_infeas_costs) {
        if (this->m_look_for_feasible_solution_only)
            return;
        this->m_costs = m_costs_backup;
        this->m_using_infeas_costs = false;
    }
    
    this->init_reduced_costs_for_one_iteration();
}

template <typename T, typename X>    void lp_primal_core_solver<T, X>::change_slope_on_breakpoint(unsigned entering, breakpoint<X> * b, T & slope_at_entering) {
    if (b->m_j == entering) {
        lp_assert(b->m_type != fixed_break && (!is_zero(b->m_delta)));
        slope_at_entering += m_sign_of_entering_delta;
        return;
    }

    lp_assert(this->m_basis_heading[b->m_j] >= 0);
    unsigned i_row = this->m_basis_heading[b->m_j];
    const T & d = - this->m_ed[i_row];
    if (numeric_traits<T>::is_zero(d)) return;

    T delta = m_sign_of_entering_delta * abs(d);
    switch (b->m_type) {
    case fixed_break:
        if (is_zero(b->m_delta)) {
            slope_at_entering += delta;
        } else {
            slope_at_entering += 2 * delta;
        }
        break;
    case low_break:
    case upper_break:
        slope_at_entering += delta;
        break;
    default:
        lp_assert(false);
    }
}


template <typename T, typename X>    void lp_primal_core_solver<T, X>::try_add_breakpoint_in_row(unsigned i) {
    lp_assert(i < this->m_m());
    const T & d = this->m_ed[i]; // the coefficient before m_entering in the i-th row
    if (d == 0) return; // the change of x[m_entering] will not change the corresponding basis x
    unsigned j = this->m_basis[i];
    const X & x = this->m_x[j];
    switch (this->m_column_types[j]) {
    case column_type::fixed:
        try_add_breakpoint(j, x, d, fixed_break, this->m_lower_bounds[j]);
        break;
    case column_type::boxed:
        try_add_breakpoint(j, x, d, low_break, this->m_lower_bounds[j]);
        try_add_breakpoint(j, x, d, upper_break, this->m_upper_bounds[j]);
        break;
    case column_type::lower_bound:
        try_add_breakpoint(j, x, d, low_break, this->m_lower_bounds[j]);
        break;
    case column_type::upper_bound:
        try_add_breakpoint(j, x, d, upper_break, this->m_upper_bounds[j]);
        break;
    case column_type::free_column:
        break;
    default:
        lp_assert(false);
        break;
    }
}


template <typename T, typename X> void lp_primal_core_solver<T, X>::print_bound_info_and_x(unsigned j, std::ostream & out) {
    out << "type of " << this->column_name(j) << " is " << column_type_to_string(this->m_column_types[j]) << std::endl;
    out << "x[" << this->column_name(j) << "] = " << this->m_x[j] << std::endl;
    switch (this->m_column_types[j]) {
    case column_type::fixed:
    case column_type::boxed:
        out << "[" << this->m_lower_bounds[j] << "," << this->m_upper_bounds[j] << "]" << std::endl;
        break;
    case column_type::lower_bound:
        out << "[" << this->m_lower_bounds[j] << ", inf" << std::endl;
        break;
    case column_type::upper_bound:
        out << "inf ," << this->m_upper_bounds[j] << "]" << std::endl;
        break;
    case column_type::free_column:
        out << "inf, inf" << std::endl;
        break;
    default:
        lp_assert(false);
        break;
    }
}


}
