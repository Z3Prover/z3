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

#include <list>
#include "util/vector.h"
#include <fstream>
#include <algorithm>
#include <set>
#include <string>
#include "math/lp/lp_primal_core_solver.h"
#include "math/lp/dense_matrix.h"
namespace lp {
// This core solver solves (Ax=b, lower_bound_values \leq x \leq upper_bound_values, maximize costs*x )
// The right side b is given implicitly by x and the basis

template <typename T, typename X>
void lp_primal_core_solver<T, X>::sort_non_basis() {
     std::sort(this->m_nbasis.begin(), this->m_nbasis.end(), [this](unsigned a, unsigned b) {
                unsigned ca = this->m_A.number_of_non_zeroes_in_column(a);
                unsigned cb = this->m_A.number_of_non_zeroes_in_column(b);
                if (ca == 0 && cb != 0) return false;
                if (ca != 0 && cb == 0) return true;
                return ca < cb;
            });
    m_non_basis_list.resize(this->m_nbasis.size());
    // initialize m_non_basis_list from m_nbasis by using an iterator on m_non_basis_list
    auto it = m_non_basis_list.begin();
    unsigned j = 0;
    for (; j < this->m_nbasis.size(); j++, ++it) {
        unsigned col = *it = this->m_nbasis[j];
        this->m_basis_heading[col] = -static_cast<int>(j) - 1;
    }
}

template <typename T, typename X>
bool lp_primal_core_solver<T, X>::correctly_moved_to_bounds(unsigned j) const {
    switch (this->m_column_types[j]) {
    case column_type::fixed:
        return this->m_x[j] == this->m_lower_bounds[j];
    case column_type::boxed:
        return this->m_x[j] == this->m_lower_bounds[j] || this->m_x[j] == this->m_upper_bounds[j];
    case column_type::lower_bound:
        return this->m_x[j] == this->m_lower_bounds[j];
    case column_type::upper_bound:
        return this->m_x[j] == this->m_upper_bounds[j];
    case column_type::free_column:
        return true;
    default:
        UNREACHABLE();
        return false;
    }
}


template <typename T, typename X>
bool lp_primal_core_solver<T, X>::column_is_benefitial_for_entering_basis(unsigned j) const {
    const T& dj = this->m_d[j];
    if (dj.is_zero()) return false;
    TRACE("lar_solver", tout << "d[" << j <<"] = " << dj << "\n";); 
    SASSERT(correctly_moved_to_bounds(j));
    switch (this->m_column_types[j]) {
    case column_type::fixed:  break;
    case column_type::free_column:
        return true;
    case column_type::lower_bound:
        if (dj > zero_of_type<T>()) return true;
        break;
    case column_type::upper_bound:
        if (dj < zero_of_type<T>()) return true;
        break;
    case column_type::boxed:
        if (dj > zero_of_type<T>() && this->m_x[j] == this->m_lower_bounds[j])
            return true;
        if (dj < zero_of_type<T>() && this->m_x[j] == this->m_upper_bounds[j])
            return true;
        break;
    default:
        UNREACHABLE();
        break;
    }
    return false;
}
// we assume that the columns are at their bounds
template <typename T, typename X> bool lp_primal_core_solver<T, X>::try_jump_to_another_bound_on_entering(unsigned entering, X & theta) {
    if (this->m_column_types[entering] != column_type::boxed)
        return false;
    X t = this->m_upper_bounds[entering] - this->m_lower_bounds[entering];
    if (t <= theta) {
        theta = t;
        return true;
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

#ifdef Z3DEBUG
template <typename T, typename X>   void lp_primal_core_solver<T, X>::check_Ax_equal_b() {
    dense_matrix<T, X> d(this->m_A);
    T * ls = d.apply_from_left_with_different_dims(this->m_x);
    SASSERT(vectors_are_equal<T>(ls, this->m_b, this->m_m()));
    delete [] ls;
}
template <typename T, typename X>    void lp_primal_core_solver<T, X>::check_the_bounds() {
    for (unsigned i = 0; i < this->m_n(); i++) {
        check_bound(i);
    }
}

template <typename T, typename X>    void lp_primal_core_solver<T, X>::check_bound(unsigned i) {
    SASSERT (!(this->column_has_lower_bound(i) && (numeric_traits<T>::zero() > this->m_x[i])));
    SASSERT (!(this->column_has_upper_bound(i) && (this->m_upper_bounds[i] < this->m_x[i])));
}

template <typename T, typename X>    void lp_primal_core_solver<T, X>::check_correctness() {
    check_the_bounds();
    check_Ax_equal_b();
}
#endif


template <typename T, typename X>    void lp_primal_core_solver<T, X>::backup_and_normalize_costs() {
    if (this->m_look_for_feasible_solution_only)
        return; // no need to backup cost, since we are going to use only feasibility costs
    m_costs_backup = this->m_costs;    
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



// calling it stage1 is too cryptic
template <typename T, typename X>    void lp_primal_core_solver<T, X>::find_feasible_solution() {
    this->m_look_for_feasible_solution_only = true;
    SASSERT(this->non_basic_columns_are_set_correctly());
    this->set_status(lp_status::UNKNOWN);
    solve();
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
        UNREACHABLE();
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
        UNREACHABLE();
        break;
    }
}


}
