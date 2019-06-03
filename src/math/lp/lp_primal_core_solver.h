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
#include <limits>
#include <unordered_map>
#include <sstream>
#include <string>
#include "util/vector.h"
#include <set>
#include <math.h>
#include <cstdlib>
#include <algorithm>
#include "math/lp/lu.h"
#include "math/lp/lp_solver.h"
#include "math/lp/static_matrix.h"
#include "math/lp/core_solver_pretty_printer.h"
#include "math/lp/lp_core_solver_base.h"
#include "math/lp/breakpoint.h"
#include "math/lp/binary_heap_priority_queue.h"
#include "math/lp/int_set.h"
namespace lp {

// This core solver solves (Ax=b, lower_bound_values \leq x \leq upper_bound_values, maximize costs*x )
// The right side b is given implicitly by x and the basis
template <typename T, typename X>
class lp_primal_core_solver:public lp_core_solver_base<T, X> {
public:
    // m_sign_of_entering is set to 1 if the entering variable needs
    // to grow and is set to -1  otherwise
    unsigned       m_column_norm_update_counter;
    T              m_enter_price_eps;
    int            m_sign_of_entering_delta;
    vector<breakpoint<X>> m_breakpoints;
    binary_heap_priority_queue<X> m_breakpoint_indices_queue;
    indexed_vector<T> m_beta; // see Swietanowski working vector beta for column norms
    T                 m_epsilon_of_reduced_cost;
    vector<T>         m_costs_backup;
    T                 m_converted_harris_eps;
    unsigned          m_inf_row_index_for_tableau;
    bool              m_bland_mode_tableau;
    int_set           m_left_basis_tableau;
    unsigned          m_bland_mode_threshold;
    unsigned          m_left_basis_repeated;
    vector<unsigned>  m_leaving_candidates;
    //    T m_converted_harris_eps = convert_struct<T, double>::convert(this->m_settings.harris_feasibility_tolerance);
    std::list<unsigned> m_non_basis_list;
    void sort_non_basis();
    void sort_non_basis_rational();
    int choose_entering_column(unsigned number_of_benefitial_columns_to_go_over);
    int choose_entering_column_tableau();
    int choose_entering_column_presize(unsigned number_of_benefitial_columns_to_go_over);
    int find_leaving_and_t_with_breakpoints(unsigned entering, X & t);
    // int find_inf_row() {
    //     // mimicing CLP : todo : use a heap
    //     int j = -1;
    //     for (unsigned k : this->m_inf_set.m_index) {
    //         if (k < static_cast<unsigned>(j))
    //             j = static_cast<int>(k);
    //     }
    //     if (j == -1)
    //         return -1;
    //     return this->m_basis_heading[j];
    //     #if 0 
    //     vector<int> choices;
    //     unsigned len = 100000000; 
    //     for (unsigned j : this->m_inf_set.m_index) {
    //         int i = this->m_basis_heading[j];
    //         lp_assert(i >= 0);
    //         unsigned row_len = this->m_A.m_rows[i].size();
    //         if (row_len < len) {
    //             choices.clear();
    //             choices.push_back(i);
    //             len = row_len;
    //             if (m_settings.random_next() % 10) break;
    //         } else if (row_len == len) {
    //             choices.push_back(i);
    //             if (m_settings.random_next() % 10) break;
    //         }
    //     }

    //     if (choices.size() == 0)
    //         return -1;

    //     if (choices.size() == 1)
    //         return choices[0];
        
    //     unsigned k = this->m_settings.random_next() % choices.size();
    //     return choices[k];
    //     #endif
    // }


    bool column_is_benefitial_for_entering_basis_on_sign_row_strategy(unsigned j, int sign) const {
        // sign = 1 means the x of the basis column of the row has to grow to become feasible, when the coeff before j is neg, or x - has to diminish when the coeff is pos
        // we have xbj = -aj * xj
        lp_assert(this->m_basis_heading[j] < 0);
        lp_assert(this->column_is_feasible(j));
        switch (this->m_column_types[j]) {
        case column_type::free_column: return true;
        case column_type::fixed: return false;
        case column_type::lower_bound:
            if (sign < 0)
                return true;
            return !this->x_is_at_lower_bound(j);
        case column_type::upper_bound:
            if (sign > 0)
                return true;
            return !this->x_is_at_upper_bound(j);
        case column_type::boxed:
            if (sign < 0)
                return !this->x_is_at_lower_bound(j);
            return !this->x_is_at_upper_bound(j);
        }

        lp_assert(false); // cannot be here
        return false;
    }
    

    bool needs_to_grow(unsigned bj) const {
        lp_assert(!this->column_is_feasible(bj));
        switch(this->m_column_types[bj]) {
        case column_type::free_column:
            return false;
        case column_type::fixed: 
        case column_type::lower_bound:
        case column_type::boxed:
            return this-> x_below_low_bound(bj);
        default:
            return false;
        }
        lp_assert(false); // unreachable
        return false;
    }

    int inf_sign_of_column(unsigned bj) const {
        lp_assert(!this->column_is_feasible(bj));
        switch(this->m_column_types[bj]) {
        case column_type::free_column:
            return 0;
        case column_type::lower_bound:
            return 1;
        case column_type::fixed: 
        case column_type::boxed:            
            return this->x_above_upper_bound(bj)? -1: 1;
        default:
            return -1;
        }
        lp_assert(false); // unreachable
        return 0;
        
    }
    

    bool monoid_can_decrease(const row_cell<T> & rc) const {
        unsigned j = rc.var();
        lp_assert(this->column_is_feasible(j));
        switch (this->m_column_types[j]) {
        case column_type::free_column:
            return true;
        case column_type::fixed:
            return false;
        case column_type::lower_bound:
            if (is_pos(rc.get_val())) {
                return this->x_above_lower_bound(j);
            }

            return true;
        case column_type::upper_bound:
            if (is_pos(rc.get_val())) {
                return true;
            }

            return this->x_below_upper_bound(j);
        case column_type::boxed:
            if (is_pos(rc.get_val())) {
                return this->x_above_lower_bound(j);
            }

            return this->x_below_upper_bound(j);
        default:
            return false;
        }
        lp_assert(false); // unreachable
        return false;
    }

    bool monoid_can_increase(const row_cell<T> & rc) const {
        unsigned j = rc.var();
        lp_assert(this->column_is_feasible(j));
        switch (this->m_column_types[j]) {
        case column_type::free_column:
            return true;
        case column_type::fixed:
            return false;
        case column_type::lower_bound:
            if (is_neg(rc.get_val())) {
                return this->x_above_lower_bound(j);
            }

            return true;
        case column_type::upper_bound:
            if (is_neg(rc.get_val())) {
                return true;
            }

            return this->x_below_upper_bound(j);
        case column_type::boxed:
            if (is_neg(rc.get_val())) {
                return this->x_above_lower_bound(j);
            }

            return this->x_below_upper_bound(j);
        default:
            return false;
        }
        lp_assert(false); // unreachable
        return false;
    }

    unsigned get_number_of_basic_vars_that_might_become_inf(unsigned j) const { // consider looking at the signs here: todo
        unsigned r = 0;
        for (const auto & cc : this->m_A.m_columns[j]) {
            unsigned k = this->m_basis[cc.var()];
            if (this->m_column_types[k] != column_type::free_column)
                r++;
        }
        return r;
    }

    
    int find_beneficial_column_in_row_tableau_rows_bland_mode(int i, T & a_ent) {
        int j = -1;
        unsigned bj = this->m_basis[i];
        bool bj_needs_to_grow = needs_to_grow(bj);
        for (const row_cell<T>& rc : this->m_A.m_rows[i]) {
            if (rc.var() == bj)
                continue;
            if (bj_needs_to_grow) {
                if (!monoid_can_decrease(rc))
                    continue;
            } else {
                if (!monoid_can_increase(rc))
                    continue;
            }
            if (rc.var() < static_cast<unsigned>(j) ) {
                j = rc.var();
                a_ent = rc.coeff();
            }
        }
        if (j == -1) {
            m_inf_row_index_for_tableau = i;
        }
            
        return j;
    }
    
    int find_beneficial_column_in_row_tableau_rows(int i, T & a_ent) {
        if (m_bland_mode_tableau)
            return find_beneficial_column_in_row_tableau_rows_bland_mode(i, a_ent);
        // a short row produces short infeasibility explanation and benefits at least one pivot operation
        int choice = -1;
        int nchoices = 0;
        unsigned num_of_non_free_basics = 1000000;
        unsigned len = 100000000;
        unsigned bj = this->m_basis[i];
        bool bj_needs_to_grow = needs_to_grow(bj);
        for (unsigned k = 0; k < this->m_A.m_rows[i].size(); k++) {
            const row_cell<T>& rc = this->m_A.m_rows[i][k];
            unsigned j = rc.var();
            if (j == bj)
                continue;
            if (bj_needs_to_grow) {
                if (!monoid_can_decrease(rc))
                    continue;
            } else {
                if (!monoid_can_increase(rc))
                    continue;
            }
            unsigned damage = get_number_of_basic_vars_that_might_become_inf(j);
            if (damage < num_of_non_free_basics) {
                num_of_non_free_basics = damage;
                len = this->m_A.m_columns[j].size();
                choice = k;
                nchoices = 1;
            } else if (damage == num_of_non_free_basics &&
                       this->m_A.m_columns[j].size() <= len && (this->m_settings.random_next() % (++nchoices))) {
                choice = k;
                len = this->m_A.m_columns[j].size();
            }
        }
        

        if (choice == -1) {
            m_inf_row_index_for_tableau = i;
            return -1;
        }
        const row_cell<T>& rc = this->m_A.m_rows[i][choice];
        a_ent = rc.coeff();
        return rc.var();
    }
    static X positive_infinity() {
        return convert_struct<X, unsigned>::convert(std::numeric_limits<unsigned>::max());
    }

    bool get_harris_theta(X & theta);

    void restore_harris_eps() { m_converted_harris_eps = convert_struct<T, double>::convert(this->m_settings.harris_feasibility_tolerance); }
    void zero_harris_eps() { m_converted_harris_eps = zero_of_type<T>(); }
    int find_leaving_on_harris_theta(X const & harris_theta, X & t);
    bool try_jump_to_another_bound_on_entering(unsigned entering, const X & theta, X & t, bool & unlimited);
    bool try_jump_to_another_bound_on_entering_unlimited(unsigned entering, X & t);
    int find_leaving_and_t(unsigned entering, X & t);
    int find_leaving_and_t_precise(unsigned entering, X & t);
    int find_leaving_and_t_tableau(unsigned entering, X & t);
 
    void limit_theta(const X & lim, X & theta, bool & unlimited) {
        if (unlimited) {
            theta = lim;
            unlimited = false;
        } else {
            theta = std::min(lim, theta);
        }
    }

    void limit_theta_on_basis_column_for_inf_case_m_neg_upper_bound(unsigned j, const T & m, X & theta, bool & unlimited) {
        lp_assert(m < 0 && this->m_column_types[j] == column_type::upper_bound);
        limit_inf_on_upper_bound_m_neg(m, this->m_x[j], this->m_upper_bounds[j], theta, unlimited);
    }


    void limit_theta_on_basis_column_for_inf_case_m_neg_lower_bound(unsigned j, const T & m, X & theta, bool & unlimited) {
        lp_assert(m < 0 && this->m_column_types[j] == column_type::lower_bound);
        limit_inf_on_bound_m_neg(m, this->m_x[j], this->m_lower_bounds[j], theta, unlimited);
    }


    void limit_theta_on_basis_column_for_inf_case_m_pos_lower_bound(unsigned j, const T & m, X & theta, bool & unlimited) {
        lp_assert(m > 0 && this->m_column_types[j] == column_type::lower_bound);
        limit_inf_on_lower_bound_m_pos(m, this->m_x[j], this->m_lower_bounds[j], theta, unlimited);
    }

    void limit_theta_on_basis_column_for_inf_case_m_pos_upper_bound(unsigned j, const T & m, X & theta, bool & unlimited) {
        lp_assert(m > 0 && this->m_column_types[j] == column_type::upper_bound);
        limit_inf_on_bound_m_pos(m, this->m_x[j], this->m_upper_bounds[j], theta, unlimited);
    };

    X harris_eps_for_bound(const X & bound) const { return ( convert_struct<X, int>::convert(1) +  abs(bound)/10) * m_converted_harris_eps/3;
    }

    void get_bound_on_variable_and_update_leaving_precisely(unsigned j, vector<unsigned> & leavings, T m, X & t, T & abs_of_d_of_leaving);

    vector<T> m_lower_bounds_dummy; // needed for the base class only

    X get_max_bound(vector<X> & b);

#ifdef Z3DEBUG
    void check_Ax_equal_b();
    void check_the_bounds();
    void check_bound(unsigned i);
    void check_correctness();
#endif

    // from page 183 of Istvan Maros's book
    // the basis structures have not changed yet
    void update_reduced_costs_from_pivot_row(unsigned entering, unsigned leaving);

    // return 0 if the reduced cost at entering is close enough to the refreshed
    // 1 if it is way off, and 2 if it is unprofitable
    int refresh_reduced_cost_at_entering_and_check_that_it_is_off(unsigned entering);

    void backup_and_normalize_costs();

    void init_run();

    void calc_working_vector_beta_for_column_norms();

    void advance_on_entering_and_leaving(int entering, int leaving, X & t);
    void advance_on_entering_and_leaving_tableau(int entering, int leaving, X & t);
    void advance_on_entering_equal_leaving(int entering, X & t);
    void advance_on_entering_equal_leaving_tableau(int entering, X & t);

    bool need_to_switch_costs() const {
        if (this->m_settings.simplex_strategy() == simplex_strategy_enum::tableau_rows)
            return false;
        //        lp_assert(calc_current_x_is_feasible() == current_x_is_feasible());
        return this->current_x_is_feasible() == this->m_using_infeas_costs;
    }


    void advance_on_entering(int entering);
    void advance_on_entering_tableau(int entering);
    void advance_on_entering_precise(int entering);
    void push_forward_offset_in_non_basis(unsigned & offset_in_nb);

    unsigned get_number_of_non_basic_column_to_try_for_enter();

    void print_column_norms(std::ostream & out);

    // returns the number of iterations
    unsigned solve();

    lu<static_matrix<T, X>> * factorization() {return this->m_factorization;}

    void delete_factorization();

    // according to Swietanowski, " A new steepest edge approximation for the simplex method for linear programming"
    void init_column_norms();

    T calculate_column_norm_exactly(unsigned j);

    void update_or_init_column_norms(unsigned entering, unsigned leaving);

    // following Swietanowski - A new steepest ...
    void update_column_norms(unsigned entering, unsigned leaving);

    T calculate_norm_of_entering_exactly();

    void find_feasible_solution();

    // bool is_tiny() const {return this->m_m < 10 && this->m_n < 20;}

    void one_iteration();
    void one_iteration_tableau();

    void advance_on_entering_and_leaving_tableau_rows(int entering, int leaving, const X &theta ) {
        this->update_basis_and_x_tableau(entering, leaving, theta);
        this->track_column_feasibility(entering);
    }


    int find_leaving_tableau_rows(X & new_val_for_leaving) {
        int j = -1;
        for (unsigned k : this->m_inf_set.m_index) {
            if (k < static_cast<unsigned>(j))
                j = static_cast<int>(k);
        }
        if (j == -1)
            return -1;

        lp_assert(!this->column_is_feasible(j));
        switch (this->m_column_types[j]) {
        case column_type::fixed:
        case column_type::upper_bound:
            new_val_for_leaving = this->m_upper_bounds[j];
            break;
        case column_type::lower_bound:
            new_val_for_leaving = this->m_lower_bounds[j];
            break;
        case column_type::boxed:
            if (this->x_above_upper_bound(j))
                new_val_for_leaving = this->m_upper_bounds[j];
            else
                new_val_for_leaving = this->m_lower_bounds[j];
            break;
        default:
            lp_assert(false);
            new_val_for_leaving = numeric_traits<X>::zero(); // does not matter
        }
        return j;
    }
    
    void one_iteration_tableau_rows() {
        X new_val_for_leaving;
        int leaving = find_leaving_tableau_rows(new_val_for_leaving);
        if (leaving == -1) {
            this->set_status(lp_status::OPTIMAL);
            return;
        }

        if (!m_bland_mode_tableau) {
            if (m_left_basis_tableau.contains(leaving)) {
                if (++m_left_basis_repeated > m_bland_mode_threshold) {
                    m_bland_mode_tableau = true;
                }
            } else {
                m_left_basis_tableau.insert(leaving);
            }
        }
        T a_ent;
        int entering = find_beneficial_column_in_row_tableau_rows(this->m_basis_heading[leaving], a_ent);
        if (entering == -1) {
            this->set_status(lp_status::INFEASIBLE);
            return;
        }
        X theta = (this->m_x[leaving] - new_val_for_leaving) / a_ent;
        advance_on_entering_and_leaving_tableau_rows(entering, leaving, theta );
        lp_assert(this->m_x[leaving] == new_val_for_leaving);
        if (this->current_x_is_feasible())
            this->set_status(lp_status::OPTIMAL);
    }

    void fill_breakpoints_array(unsigned entering);

    void try_add_breakpoint_in_row(unsigned i);

    void clear_breakpoints();

    void change_slope_on_breakpoint(unsigned entering, breakpoint<X> * b, T & slope_at_entering);
    void advance_on_sorted_breakpoints(unsigned entering);

    void update_basis_and_x_with_comparison(unsigned entering, unsigned leaving, X delta);

    void decide_on_status_when_cannot_find_entering() {
        lp_assert(!need_to_switch_costs());
        this->set_status(this->current_x_is_feasible()? lp_status::OPTIMAL: lp_status::INFEASIBLE);
    }

    // void limit_theta_on_basis_column_for_feas_case_m_neg(unsigned j, const T & m, X & theta) {
    //     lp_assert(m < 0);
    //     lp_assert(this->m_column_type[j] == lower_bound || this->m_column_type[j] == boxed);
    //     const X & eps = harris_eps_for_bound(this->m_lower_bounds[j]);
    //     if (this->above_bound(this->m_x[j], this->m_lower_bounds[j])) {
    //         theta = std::min((this->m_lower_bounds[j] -this->m_x[j] - eps) / m, theta);
    //         if (theta < zero_of_type<X>()) theta = zero_of_type<X>();
    //     }
    // }

    void limit_theta_on_basis_column_for_feas_case_m_neg_no_check(unsigned j, const T & m, X & theta, bool & unlimited) {
        lp_assert(m < 0);
        const X& eps = harris_eps_for_bound(this->m_lower_bounds[j]);
        limit_theta((this->m_lower_bounds[j] - this->m_x[j] - eps) / m, theta, unlimited);
        if (theta < zero_of_type<X>()) theta = zero_of_type<X>();
    }

    bool limit_inf_on_bound_m_neg(const T & m, const X & x, const X & bound, X & theta, bool & unlimited) {
        // x gets smaller
        lp_assert(m < 0);
        if (numeric_traits<T>::precise()) {
            if (this->below_bound(x, bound)) return false;
            if (this->above_bound(x, bound)) {
                limit_theta((bound - x) / m, theta, unlimited);
            } else {
                theta = zero_of_type<X>();
                unlimited = false;
            }
        } else {
            const X& eps = harris_eps_for_bound(bound);
            if (this->below_bound(x, bound)) return false;
            if (this->above_bound(x, bound)) {
                limit_theta((bound - x - eps) / m, theta, unlimited);
            } else {
                theta = zero_of_type<X>();
                unlimited = false;
            }
        }
        return true;
    }

    bool limit_inf_on_bound_m_pos(const T & m, const X & x, const X & bound, X & theta, bool & unlimited) {
        // x gets larger
        lp_assert(m > 0);
        if (numeric_traits<T>::precise()) {
            if (this->above_bound(x, bound)) return false;
            if (this->below_bound(x, bound)) {
                limit_theta((bound - x) / m, theta, unlimited);
            } else {
                theta = zero_of_type<X>();
                unlimited = false;
            }
        } else {
            const X& eps = harris_eps_for_bound(bound);
            if (this->above_bound(x, bound)) return false;
            if (this->below_bound(x, bound)) {
                limit_theta((bound - x + eps) / m, theta, unlimited);
            } else {
                theta = zero_of_type<X>();
                unlimited = false;
            }
        }
        return true;
    }

    void limit_inf_on_lower_bound_m_pos(const T & m, const X & x, const X & bound, X & theta, bool & unlimited) {
        if (numeric_traits<T>::precise()) {
            // x gets larger
            lp_assert(m > 0);
            if (this->below_bound(x, bound)) {
                limit_theta((bound - x) / m, theta, unlimited);
            }
        }
        else {
            // x gets larger
            lp_assert(m > 0);
            const X& eps = harris_eps_for_bound(bound);
            if (this->below_bound(x, bound)) {
                limit_theta((bound - x + eps) / m, theta, unlimited);
            }
        }
    }

    void limit_inf_on_upper_bound_m_neg(const T & m, const X & x, const X & bound, X & theta, bool & unlimited) {
        // x gets smaller
        lp_assert(m < 0);
        const X& eps = harris_eps_for_bound(bound);
        if (this->above_bound(x, bound)) {
            limit_theta((bound - x - eps) / m, theta, unlimited);
        }
    }

    void limit_theta_on_basis_column_for_inf_case_m_pos_boxed(unsigned j, const T & m, X & theta, bool & unlimited) {
        //        lp_assert(m > 0 && this->m_column_type[j] == column_type::boxed);
        const X & x = this->m_x[j];
        const X & lbound = this->m_lower_bounds[j];

        if (this->below_bound(x, lbound)) {
            const X& eps = harris_eps_for_bound(this->m_upper_bounds[j]);
            limit_theta((lbound - x + eps) / m, theta, unlimited);
        } else {
            const X & ubound = this->m_upper_bounds[j];
            if (this->below_bound(x, ubound)){
                const X& eps = harris_eps_for_bound(ubound);
                limit_theta((ubound - x + eps) / m, theta, unlimited);
            } else if (!this->above_bound(x, ubound)) {
                theta = zero_of_type<X>();
                unlimited = false;
            }
        }
    }

    void limit_theta_on_basis_column_for_inf_case_m_neg_boxed(unsigned j, const T & m, X & theta, bool & unlimited) {
        //  lp_assert(m < 0 && this->m_column_type[j] == column_type::boxed);
        const X & x = this->m_x[j];
        const X & ubound = this->m_upper_bounds[j];
        if (this->above_bound(x, ubound)) {
            const X& eps = harris_eps_for_bound(ubound);
            limit_theta((ubound - x - eps) / m, theta, unlimited);
        } else {
            const X & lbound = this->m_lower_bounds[j];
            if (this->above_bound(x, lbound)){
                const X& eps = harris_eps_for_bound(lbound);
                limit_theta((lbound - x - eps) / m, theta, unlimited);
            } else if (!this->below_bound(x, lbound)) {
                theta = zero_of_type<X>();
                unlimited = false;
            }
        }
    }
    void limit_theta_on_basis_column_for_feas_case_m_pos(unsigned j, const T & m, X & theta, bool & unlimited) {
        lp_assert(m > 0);
        const T& eps = harris_eps_for_bound(this->m_upper_bounds[j]);
        if (this->below_bound(this->m_x[j], this->m_upper_bounds[j])) {
            limit_theta((this->m_upper_bounds[j] - this->m_x[j] + eps) / m, theta, unlimited);
            if (theta < zero_of_type<X>()) {
                theta = zero_of_type<X>();
                unlimited = false;
            }
        }
    }

    void limit_theta_on_basis_column_for_feas_case_m_pos_no_check(unsigned j, const T & m, X & theta, bool & unlimited ) {
        lp_assert(m > 0);
        const X& eps = harris_eps_for_bound(this->m_upper_bounds[j]);
        limit_theta( (this->m_upper_bounds[j] - this->m_x[j] + eps) / m, theta, unlimited);
        if (theta < zero_of_type<X>()) {
            theta = zero_of_type<X>();
        }
    }

    // j is a basic column or the entering, in any case x[j] has to stay feasible.
    // m is the multiplier. updating t in a way that holds the following
    // x[j] + t * m >=  this->m_lower_bounds[j]- harris_feasibility_tolerance ( if m < 0 )
    // or
    // x[j] + t * m <= this->m_upper_bounds[j] + harris_feasibility_tolerance ( if m > 0)
    void limit_theta_on_basis_column(unsigned j, T m, X & theta, bool & unlimited) {
        switch (this->m_column_types[j]) {
        case column_type::free_column: break;
        case column_type::upper_bound:
            if (this->current_x_is_feasible()) {
                if (m > 0)
                    limit_theta_on_basis_column_for_feas_case_m_pos_no_check(j, m, theta, unlimited);
            } else { // inside of feasibility_loop
                if (m > 0)
                    limit_theta_on_basis_column_for_inf_case_m_pos_upper_bound(j, m, theta, unlimited);
                else
                    limit_theta_on_basis_column_for_inf_case_m_neg_upper_bound(j, m, theta, unlimited);
            }
            break;
        case column_type::lower_bound:
            if (this->current_x_is_feasible()) {
                if (m < 0)
                    limit_theta_on_basis_column_for_feas_case_m_neg_no_check(j, m, theta, unlimited);
            } else {
                if (m < 0)
                    limit_theta_on_basis_column_for_inf_case_m_neg_lower_bound(j, m, theta, unlimited);
                else
                    limit_theta_on_basis_column_for_inf_case_m_pos_lower_bound(j, m, theta, unlimited);
            }
            break;
            // case fixed:
            //     if (get_this->current_x_is_feasible()) {
            //         theta = zero_of_type<X>();
            //         break;
            //     }
            //     if (m < 0)
            //         limit_theta_on_basis_column_for_inf_case_m_neg_fixed(j, m, theta);
            //     else
            //         limit_theta_on_basis_column_for_inf_case_m_pos_fixed(j, m, theta);
            //     break;
        case column_type::fixed:
        case column_type::boxed:
            if (this->current_x_is_feasible()) {
                if (m > 0) {
                    limit_theta_on_basis_column_for_feas_case_m_pos_no_check(j, m, theta, unlimited);
                } else {
                    limit_theta_on_basis_column_for_feas_case_m_neg_no_check(j, m, theta, unlimited);
                }
            } else {
                if (m > 0) {
                    limit_theta_on_basis_column_for_inf_case_m_pos_boxed(j, m, theta, unlimited);
                } else {
                    limit_theta_on_basis_column_for_inf_case_m_neg_boxed(j, m, theta, unlimited);
                }
            }

            break;
        default:
            lp_unreachable();
        }
        if (!unlimited && theta < zero_of_type<X>()) {
            theta = zero_of_type<X>();
        }
    }

    
    bool column_is_benefitial_for_entering_basis(unsigned j) const;
    bool column_is_benefitial_for_entering_basis_precise(unsigned j) const;

    bool column_is_benefitial_for_entering_on_breakpoints(unsigned j) const;


    bool can_enter_basis(unsigned j);
    bool done();
    void init_infeasibility_costs();
    
    void init_infeasibility_cost_for_column(unsigned j);
    T get_infeasibility_cost_for_column(unsigned j) const;
    void init_infeasibility_costs_for_changed_basis_only();

    void print_column(unsigned j, std::ostream & out);
    void add_breakpoint(unsigned j, X delta, breakpoint_type type);

    // j is the basic column, x is the value at x[j]
    // d is the coefficient before m_entering in the row with j as the basis column
    void try_add_breakpoint(unsigned j, const X & x, const T & d, breakpoint_type break_type, const X & break_value);
    template <typename L>
    bool same_sign_with_entering_delta(const L & a) {
        return (a > zero_of_type<L>() && m_sign_of_entering_delta > 0) || (a < zero_of_type<L>() && m_sign_of_entering_delta < 0);
    }

    void init_reduced_costs();

    bool lower_bounds_are_set() const override { return true; }

    int advance_on_sorted_breakpoints(unsigned entering, X & t);
    
    std::string break_type_to_string(breakpoint_type type);

    void print_breakpoint(const breakpoint<X> * b, std::ostream & out);

    void print_bound_info_and_x(unsigned j, std::ostream & out);

    void init_infeasibility_after_update_x_if_inf(unsigned leaving) {
        if (this->m_using_infeas_costs) {
            init_infeasibility_costs_for_changed_basis_only();
            this->m_costs[leaving] = zero_of_type<T>();
            this->m_inf_set.erase(leaving);
        } 
    }
    
    void init_inf_set() {
        this->m_inf_set.clear();
        for (unsigned j = 0; j < this->m_n(); j++) {
            if (this->m_basis_heading[j] < 0)
                continue;
            if (!this->column_is_feasible(j))
                this->insert_column_into_inf_set(j);
        }
    }

    int get_column_out_of_bounds_delta_sign(unsigned j) {
        switch (this->m_column_types[j]) {
        case column_type::fixed:
        case column_type::boxed:
            if (this->x_below_low_bound(j))
                return -1;
            if (this->x_above_upper_bound(j))
                return 1;
            break;
        case column_type::lower_bound:
            if (this->x_below_low_bound(j))
                return -1;
            break;
        case column_type::upper_bound:
            if (this->x_above_upper_bound(j))
                return 1;
            break;
        case column_type::free_column:
            return 0;
        default:
            lp_assert(false);
        }
        return 0;
    }

    void init_column_row_non_zeroes() {
        this->m_columns_nz.resize(this->m_A.column_count());
        this->m_rows_nz.resize(this->m_A.row_count());
        for (unsigned i = 0; i < this->m_A.column_count(); i++) {
            if (this->m_columns_nz[i] == 0)
                this->m_columns_nz[i] = this->m_A.m_columns[i].size();
        }
        for (unsigned i = 0; i < this->m_A.row_count(); i++) {
         if (this->m_rows_nz[i] == 0)
            this->m_rows_nz[i] = this->m_A.m_rows[i].size();
        }
    }
    

    int x_at_bound_sign(unsigned j) {
        switch (this->m_column_types[j]) {
        case column_type::fixed:
            return 0;
        case column_type::boxed:
            if (this->x_is_at_lower_bound(j))
                return 1;
            return -1;
            break;
        case column_type::lower_bound:
            return 1;
            break;
        case column_type::upper_bound:
            return -1;
            break;
        default:
            lp_assert(false);
        }
        return 0;

    }

    unsigned solve_with_tableau();

    bool basis_column_is_set_correctly(unsigned j) const {
        return this->m_A.m_columns[j].size() == 1;
            
    }
    
    bool basis_columns_are_set_correctly() const {
        for (unsigned j : this->m_basis)
            if(!basis_column_is_set_correctly(j))
                return false;
        
        return this->m_basis_heading.size() == this->m_A.column_count() && this->m_basis.size() == this->m_A.row_count();
    }

    void init_run_tableau();
    void update_x_tableau(unsigned entering, const X & delta);
    void update_inf_cost_for_column_tableau(unsigned j);

// the delta is between the old and the new cost (old - new)
    void update_reduced_cost_for_basic_column_cost_change(const T & delta, unsigned j) {
        lp_assert(this->m_basis_heading[j] >= 0);
        unsigned i = static_cast<unsigned>(this->m_basis_heading[j]);
        for (const row_cell<T> & rc : this->m_A.m_rows[i]) {
            unsigned k = rc.var();
            if (k == j)
                continue;
            this->m_d[k] += delta * rc.get_val();
        }
    }
    
    bool update_basis_and_x_tableau(int entering, int leaving, X const & tt);
    void init_reduced_costs_tableau();
    void init_tableau_rows() {
        m_bland_mode_tableau = false;
        m_left_basis_tableau.clear();
        m_left_basis_tableau.resize(this->m_A.column_count());
        m_left_basis_repeated = 0;
    }
// stage1 constructor
    lp_primal_core_solver(static_matrix<T, X> & A,
                          vector<X> & b, // the right side vector
                          vector<X> & x, // the number of elements in x needs to be at least as large as the number of columns in A
                          vector<unsigned> & basis,
                          vector<unsigned> & nbasis,
                          vector<int> & heading,
                          vector<T> & costs,
                          const vector<column_type> & column_type_array,
                          const vector<X> & lower_bound_values,
                          const vector<X> & upper_bound_values,
                          lp_settings & settings,
                          const column_namer& column_names):
        lp_core_solver_base<T, X>(A, b,
                                  basis,
                                  nbasis,
                                  heading,
                                  x,
                                  costs,
                                  settings,
                                  column_names,
                                  column_type_array,
                                  lower_bound_values,
                                  upper_bound_values),
        m_beta(A.row_count()),
        m_epsilon_of_reduced_cost(T(1)/T(10000000)),
        m_bland_mode_threshold(1000) {

        if (!(numeric_traits<T>::precise())) {
            m_converted_harris_eps = convert_struct<T, double>::convert(this->m_settings.harris_feasibility_tolerance);
        } else {
            m_converted_harris_eps = zero_of_type<T>();
        }
        this->set_status(lp_status::UNKNOWN);
    }

    // constructor
    lp_primal_core_solver(static_matrix<T, X> & A,
                          vector<X> & b, // the right side vector
                          vector<X> & x, // the number of elements in x needs to be at least as large as the number of columns in A
                          vector<unsigned> & basis,
                          vector<unsigned> & nbasis,
                          vector<int> & heading,
                          vector<T> & costs,
                          const vector<column_type> & column_type_array,
                          const vector<X> & upper_bound_values,
                          lp_settings & settings,
                          const column_namer& column_names):
        lp_core_solver_base<T, X>(A, b,
                                  basis,
                                  nbasis,
                                  heading,
                                  x,
                                  costs,
                                  settings,
                                  column_names,
                                  column_type_array,
                                  m_lower_bounds_dummy,
                                  upper_bound_values),
        m_beta(A.row_count()),
        m_converted_harris_eps(convert_struct<T, double>::convert(this->m_settings.harris_feasibility_tolerance)) {
        lp_assert(initial_x_is_correct());
        m_lower_bounds_dummy.resize(A.column_count(), zero_of_type<T>());
        m_enter_price_eps = numeric_traits<T>::precise() ? numeric_traits<T>::zero() : T(1e-5);
#ifdef Z3DEBUG
        // check_correctness();
#endif
    }

    bool initial_x_is_correct() {
        std::set<unsigned> basis_set;
        for (unsigned i = 0; i < this->m_A.row_count(); i++) {
            basis_set.insert(this->m_basis[i]);
        }
        for (unsigned j = 0; j < this->m_n(); j++) {
            if (this->column_has_lower_bound(j) && this->m_x[j] < numeric_traits<T>::zero()) {
                LP_OUT(this->m_settings, "low bound for variable " << j << " does not hold: this->m_x[" << j << "] = " << this->m_x[j] << " is negative " << std::endl);
                return false;
            }

            if (this->column_has_upper_bound(j) && this->m_x[j] > this->m_upper_bounds[j]) {
                LP_OUT(this->m_settings, "upper bound for " << j << " does not hold: "  << this->m_upper_bounds[j] << ">" << this->m_x[j] << std::endl);
                return false;
            }

            if (basis_set.find(j) != basis_set.end()) continue;
            if (this->m_column_types[j] == column_type::lower_bound)  {
                if (numeric_traits<T>::zero() != this->m_x[j]) {
                    LP_OUT(this->m_settings, "only low bound is set for " << j << " but low bound value " << numeric_traits<T>::zero() << " is not equal to " << this->m_x[j] << std::endl);
                    return false;
                }
            }
            if (this->m_column_types[j] == column_type::boxed) {
                if (this->m_upper_bounds[j] != this->m_x[j] && !numeric_traits<T>::is_zero(this->m_x[j])) {
                    return false;
                }
            }
        }
        return true;
    }


    friend core_solver_pretty_printer<T, X>;
};
}
