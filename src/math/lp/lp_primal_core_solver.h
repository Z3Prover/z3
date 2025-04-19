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
#include "math/lp/core_solver_pretty_printer.h"
#include "math/lp/lp_core_solver_base.h"
#include "math/lp/static_matrix.h"
#include "util/uint_set.h"
#include "util/vector.h"
#include <algorithm>
#include <cstdlib>
#include <limits>
#include <list>
#include <math.h>
#include <set>
#include <sstream>
#include <string>
#include <unordered_map>
#include "util/heap.h"

namespace lp {

    // This core solver solves (Ax=b, lower_bound_values \leq x \leq
    // upper_bound_values, maximize costs*x ) The right side b is given implicitly
    // by x and the basis
    template <typename T, typename X>
    class lp_primal_core_solver : public lp_core_solver_base<T, X> {
    public:
        int m_sign_of_entering_delta;
        vector<T> m_costs_backup;
        unsigned m_inf_row_index_for_tableau;
        bool m_bland_mode_tableau;
        indexed_uint_set m_left_basis_tableau;
        unsigned m_bland_mode_threshold;
        unsigned m_left_basis_repeated;
        vector<unsigned> m_leaving_candidates;

        std::list<unsigned> m_non_basis_list;
        void sort_non_basis();
        int choose_entering_column_tableau();

        bool needs_to_grow(unsigned bj) const {
            SASSERT(!this->column_is_feasible(bj));
            switch (this->m_column_types[bj]) {
            case column_type::free_column:
                return false;
            case column_type::fixed:
            case column_type::lower_bound:
            case column_type::boxed:
                return this->x_below_low_bound(bj);
            default:
                return false;
            }
            UNREACHABLE(); // unreachable
            return false;
        }

        int inf_sign_of_column(unsigned bj) const {
            SASSERT(!this->column_is_feasible(bj));
            switch (this->m_column_types[bj]) {
            case column_type::free_column:
                return 0;
            case column_type::lower_bound:
                return 1;
            case column_type::fixed:
            case column_type::boxed:
                return this->x_above_upper_bound(bj) ? -1 : 1;
            default:
                return -1;
            }
            UNREACHABLE(); // unreachable
            return 0;
        }

        bool monoid_can_decrease(const row_cell<T> &rc) const {
            unsigned j = rc.var();
            SASSERT(this->column_is_feasible(j));
            switch (this->m_column_types[j]) {
            case column_type::free_column:
                return true;
            case column_type::fixed:
                return false;
            case column_type::lower_bound:
                return !is_pos(rc.coeff()) || this->x_above_lower_bound(j);
            case column_type::upper_bound:
                return is_pos(rc.coeff()) || this->x_below_upper_bound(j);
            case column_type::boxed:
                if (is_pos(rc.coeff())) 
                    return this->x_above_lower_bound(j);
                return this->x_below_upper_bound(j);
            default:
                return false;
            }
            UNREACHABLE(); // unreachable
            return false;
        }

        bool monoid_can_increase(const row_cell<T> &rc) const {
            unsigned j = rc.var();
            SASSERT(this->column_is_feasible(j));
            switch (this->m_column_types[j]) {
            case column_type::free_column:
                return true;
            case column_type::fixed:
                return false;
            case column_type::lower_bound:
                if (is_neg(rc.coeff())) 
                    return this->x_above_lower_bound(j);
                return true;
            case column_type::upper_bound:
                if (is_neg(rc.coeff())) 
                    return true;
                return this->x_below_upper_bound(j);
            case column_type::boxed:
                if (is_neg(rc.coeff())) 
                    return this->x_above_lower_bound(j);
                return this->x_below_upper_bound(j);
            default:
                return false;
            }
            UNREACHABLE(); // unreachable
            return false;
        }

        /**
         * Return the number of base non-free variables depending on the column j,
         * different from bj,
         * but take the min with the (bound+1).
         * This function is used to select the pivot variable.
         */
        unsigned get_num_of_not_free_basic_dependent_vars(unsigned j, unsigned bound, unsigned bj) const {
            // consider looking at the signs here: todo
            unsigned r = 0;
            for (const auto &cc : this->m_A.m_columns[j]) {
                unsigned basic_for_row = this->m_basis[cc.var()];
                if (basic_for_row == bj)
                    continue;

                // std::cout << this->m_A.m_rows[cc.var()] << std::endl;
                if (this->m_column_types[basic_for_row] != column_type::free_column)
                    if (r++ > bound) return r;
            }
            return r;
        }

        int find_beneficial_entering_in_row_tableau_rows_bland_mode(int i, T &a_ent) {
            int j = -1;
            unsigned bj = this->m_basis[i];
            bool bj_needs_to_grow = needs_to_grow(bj);
            for (const row_cell<T> &rc : this->m_A.m_rows[i]) {
                if (rc.var() == bj)
                    continue;
                if (bj_needs_to_grow) {
                    if (!monoid_can_decrease(rc))
                        continue;
                } 
                else {
                    if (!monoid_can_increase(rc))
                        continue;
                }
                if (rc.var() < static_cast<unsigned>(j)) {
                    j = rc.var();
                    a_ent = rc.coeff();
                }
            }
            if (j == -1)
                m_inf_row_index_for_tableau = i;
            return j;
        }

        int find_beneficial_entering_tableau_rows(int i, T &a_ent) {
            if (m_bland_mode_tableau)
            return find_beneficial_entering_in_row_tableau_rows_bland_mode(i, a_ent);
            // a short row produces short infeasibility explanation and benefits at
            // least one pivot operation
            int choice = -1;
            int nchoices = 0;
            unsigned min_non_free_so_far = -1;
            unsigned best_col_sz = -1;
            unsigned bj = this->m_basis[i];
            bool bj_needs_to_grow = needs_to_grow(bj);
            for (unsigned k = 0; k < this->m_A.m_rows[i].size(); k++) {
                const row_cell<T> &rc = this->m_A.m_rows[i][k];
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
                unsigned not_free = get_num_of_not_free_basic_dependent_vars(j, min_non_free_so_far, bj);
                unsigned col_sz = static_cast<unsigned>(this->m_A.m_columns[j].size());
                if (not_free < min_non_free_so_far || (not_free == min_non_free_so_far && col_sz < best_col_sz)) {
                    min_non_free_so_far = not_free;
                    best_col_sz = static_cast<unsigned>(this->m_A.m_columns[j].size());
                    choice = k;
                    nchoices = 1;
                } 
                else if (not_free == min_non_free_so_far &&
                       col_sz == best_col_sz) {
                    if (this->m_settings.random_next(++nchoices) == 0) 
                        choice = k;                    
                }
            }

            if (choice == -1) {
                m_inf_row_index_for_tableau = i;
                return -1;
            }
            const row_cell<T> &rc = this->m_A.m_rows[i][choice];
            a_ent = rc.coeff();
            return rc.var();
        }

    bool try_jump_to_another_bound_on_entering(unsigned entering, X &t);

    bool try_jump_to_another_bound_on_entering_unlimited(unsigned entering, X &t);

    int find_leaving_and_t_tableau(unsigned entering, X &t);

    void limit_theta(const X &lim, X &theta, bool &unlimited) {
        if (unlimited) {
            theta = lim;
            unlimited = false;
        } else
            theta = std::min(lim, theta);
    }

    void limit_theta_on_basis_column_for_inf_case_m_neg_upper_bound(
        unsigned j, const T &m, X &theta, bool &unlimited) {
        SASSERT(m < 0 && this->m_column_types[j] == column_type::upper_bound);
        limit_inf_on_upper_bound_m_neg(m, this->m_x[j], this->m_upper_bounds[j], theta, unlimited);
    }

    void limit_theta_on_basis_column_for_inf_case_m_neg_lower_bound(
        unsigned j, const T &m, X &theta, bool &unlimited) {
        SASSERT(m < 0 && this->m_column_types[j] == column_type::lower_bound);
        limit_inf_on_bound_m_neg(m, this->m_x[j], this->m_lower_bounds[j], theta, unlimited);
    }

    void limit_theta_on_basis_column_for_inf_case_m_pos_lower_bound(
        unsigned j, const T &m, X &theta, bool &unlimited) {
        SASSERT(m > 0 && this->m_column_types[j] == column_type::lower_bound);
        limit_inf_on_lower_bound_m_pos(m, this->m_x[j], this->m_lower_bounds[j], theta, unlimited);
    }

    void limit_theta_on_basis_column_for_inf_case_m_pos_upper_bound(
        unsigned j, const T &m, X &theta, bool &unlimited) {
        SASSERT(m > 0 && this->m_column_types[j] == column_type::upper_bound);
        limit_inf_on_bound_m_pos(m, this->m_x[j], this->m_upper_bounds[j], theta, unlimited);
    };

    void get_bound_on_variable_and_update_leaving_precisely(
        unsigned j, vector<unsigned> &leavings, T m, X &t,
        T &abs_of_d_of_leaving);

#ifdef Z3DEBUG
    void check_Ax_equal_b();
    void check_the_bounds();
    void check_bound(unsigned i);
    void check_correctness();
#endif

    void backup_and_normalize_costs();

    void advance_on_entering_and_leaving_tableau(int entering, int leaving, X &t);
    void advance_on_entering_equal_leaving_tableau(int entering, X &t);

    void pivot(int entering, int leaving) {
        this->pivot_column_tableau(entering, this->m_basis_heading[leaving]);
        this->change_basis(entering, leaving);
    }

    bool need_to_switch_costs() const {
        if (this->m_settings.simplex_strategy() ==
            simplex_strategy_enum::tableau_rows)
            return false;
        //        SASSERT(calc_current_x_is_feasible() ==
        //        current_x_is_feasible());
        return this->current_x_is_feasible() == this->using_infeas_costs();
    }

    void advance_on_entering_tableau(int entering);

    void push_forward_offset_in_non_basis(unsigned &offset_in_nb);

    unsigned get_number_of_non_basic_column_to_try_for_enter();

    // returns the number of iterations
    unsigned solve();

    void find_feasible_solution();

    // bool is_tiny() const {return this->m_m < 10 && this->m_n < 20;}

    void one_iteration_tableau();

    // this version assumes that the leaving already has the right value, and does
    // not update it
    void update_x_tableau_rows(unsigned entering, unsigned leaving,
                               const X &delta) {
        this->add_delta_to_x(entering, delta);
        for (const auto &c : this->m_A.m_columns[entering])
            if (leaving != this->m_basis[c.var()])
                this->add_delta_to_x_and_track_feasibility(
                    this->m_basis[c.var()], -delta * this->m_A.get_val(c));
    }

    void update_basis_and_x_tableau_rows(int entering, int leaving, X const &tt) {
        SASSERT(entering != leaving);
        update_x_tableau_rows(entering, leaving, tt);
        this->pivot_column_tableau(entering, this->m_basis_heading[leaving]);
        this->change_basis(entering, leaving);
    }

    void advance_on_entering_and_leaving_tableau_rows(int entering, int leaving,
                                                      const X &theta) {
        update_basis_and_x_tableau_rows(entering, leaving, theta);
        this->track_column_feasibility(entering);
    }

    int find_smallest_inf_column() {
        if (this->inf_heap().empty())
            return -1;

        return this->inf_heap().min_value();
    }

    const X &get_val_for_leaving(unsigned j) const {
        SASSERT(!this->column_is_feasible(j));
        switch (this->m_column_types[j]) {
            case column_type::fixed:
            case column_type::upper_bound:
                return this->m_upper_bounds[j];
            case column_type::lower_bound:
                return this->m_lower_bounds[j];
                break;
            case column_type::boxed:
                if (this->x_above_upper_bound(j))
                    return this->m_upper_bounds[j];
                else
                    return this->m_lower_bounds[j];
                break;
            default:
                UNREACHABLE();
                return this->m_lower_bounds[j];
        }
    }

    void one_iteration_tableau_rows() {
        int leaving = find_smallest_inf_column();
        if (leaving == -1) {
            this->set_status(lp_status::OPTIMAL);
            return;
        }

        SASSERT(this->column_is_base(leaving));

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
        int entering = find_beneficial_entering_tableau_rows(
            this->m_basis_heading[leaving], a_ent);
        if (entering == -1) {
            this->set_status(lp_status::INFEASIBLE);
            return;
        }
        const X &new_val_for_leaving = get_val_for_leaving(leaving);
        X theta = (this->m_x[leaving] - new_val_for_leaving) / a_ent;
        this->m_x[leaving] = new_val_for_leaving;
        TRACE("lar_solver_feas", tout << "entering = " << entering << ", leaving = " << leaving << ", new_val_for_leaving = " << new_val_for_leaving << ", theta = " << theta << "\n";);
        TRACE("lar_solver_feas", tout << "leaving = " << leaving
                                 << " removed from inf_heap()\n";);
        // this will remove the leaving from the heap
        this->inf_heap().erase_min();
        advance_on_entering_and_leaving_tableau_rows(entering, leaving, theta);
        if (this->current_x_is_feasible())
            this->set_status(lp_status::OPTIMAL);
    }

    void decide_on_status_when_cannot_find_entering() {
        this->set_status(this->current_x_is_feasible() ? lp_status::OPTIMAL
                                                       : lp_status::INFEASIBLE);
    }

    void limit_theta_on_basis_column_for_feas_case_m_neg_no_check(
        unsigned j, const T &m, X &theta, bool &unlimited) {
        SASSERT(m < 0);
        limit_theta((this->m_lower_bounds[j] - this->m_x[j]) / m, theta, unlimited);
        if (theta < zero_of_type<X>())
            theta = zero_of_type<X>();
    }

    bool limit_inf_on_bound_m_neg(const T &m, const X &x, const X &bound,
                                  X &theta, bool &unlimited) {
        // x gets smaller
        SASSERT(m < 0);
        if (this->below_bound(x, bound))
            return false;
        if (this->above_bound(x, bound)) {
            limit_theta((bound - x) / m, theta, unlimited);
        } else {
            theta = zero_of_type<X>();
            unlimited = false;
        }
        return true;
    }

    bool limit_inf_on_bound_m_pos(const T &m, const X &x, const X &bound,
                                  X &theta, bool &unlimited) {
        // x gets larger
        SASSERT(m > 0);
        if (this->above_bound(x, bound))
            return false;
        if (this->below_bound(x, bound)) {
            limit_theta((bound - x) / m, theta, unlimited);
        } else {
            theta = zero_of_type<X>();
            unlimited = false;
        }

        return true;
    }

    void limit_inf_on_lower_bound_m_pos(const T &m, const X &x, const X &bound,
                                        X &theta, bool &unlimited) {
        // x gets larger
        SASSERT(m > 0);
        if (this->below_bound(x, bound)) {
            limit_theta((bound - x) / m, theta, unlimited);
        }
    }

    void limit_inf_on_upper_bound_m_neg(const T &m, const X &x, const X &bound,
                                        X &theta, bool &unlimited) {
        // x gets smaller
        SASSERT(m < 0);
        if (this->above_bound(x, bound)) {
            limit_theta((bound - x) / m, theta, unlimited);
        }
    }

    void limit_theta_on_basis_column_for_inf_case_m_pos_boxed(unsigned j,
                                                              const T &m,
                                                              X &theta,
                                                              bool &unlimited) {
        const X &x = this->m_x[j];
        const X &lbound = this->m_lower_bounds[j];

        if (this->below_bound(x, lbound)) {
            limit_theta((lbound - x) / m, theta, unlimited);
        } else {
            const X &ubound = this->m_upper_bounds[j];
            if (this->below_bound(x, ubound)) {
                limit_theta((ubound - x) / m, theta, unlimited);
            } else if (!this->above_bound(x, ubound)) {
                theta = zero_of_type<X>();
                unlimited = false;
            }
        }
    }

    void limit_theta_on_basis_column_for_inf_case_m_neg_boxed(unsigned j,
                                                              const T &m,
                                                              X &theta,
                                                              bool &unlimited) {
        //  SASSERT(m < 0 && this->m_column_type[j] == column_type::boxed);
        const X &x = this->m_x[j];
        const X &ubound = this->m_upper_bounds[j];
        if (this->above_bound(x, ubound)) {
            limit_theta((ubound - x) / m, theta, unlimited);
        } else {
            const X &lbound = this->m_lower_bounds[j];
            if (this->above_bound(x, lbound)) {
                limit_theta((lbound - x) / m, theta, unlimited);
            } else if (!this->below_bound(x, lbound)) {
                theta = zero_of_type<X>();
                unlimited = false;
            }
        }
    }

    void limit_theta_on_basis_column_for_feas_case_m_pos_no_check(
        unsigned j, const T &m, X &theta, bool &unlimited) {
        SASSERT(m > 0);
        limit_theta((this->m_upper_bounds[j] - this->m_x[j]) / m, theta, unlimited);
        if (theta < zero_of_type<X>()) {
            theta = zero_of_type<X>();
        }
    }

    // j is a basic column or the entering, in any case x[j] has to stay feasible.
    // m is the multiplier. updating t in a way that holds the following
    // x[j] + t * m >=  this->m_lower_bounds[j]( if m < 0 )
    // or
    // x[j] + t * m <= this->m_upper_bounds[j]  ( if m > 0)
    void limit_theta_on_basis_column(unsigned j, T m, X &theta, bool &unlimited) {
        switch (this->m_column_types[j]) {
            case column_type::free_column:
                break;
            case column_type::upper_bound:
                if (this->current_x_is_feasible()) {
                    if (m > 0)
                        limit_theta_on_basis_column_for_feas_case_m_pos_no_check(j, m, theta,
                                                                                 unlimited);
                } else {  // inside of feasibility_loop
                    if (m > 0)
                        limit_theta_on_basis_column_for_inf_case_m_pos_upper_bound(
                            j, m, theta, unlimited);
                    else
                        limit_theta_on_basis_column_for_inf_case_m_neg_upper_bound(
                            j, m, theta, unlimited);
                }
                break;
            case column_type::lower_bound:
                if (this->current_x_is_feasible()) {
                    if (m < 0)
                        limit_theta_on_basis_column_for_feas_case_m_neg_no_check(j, m, theta,
                                                                                 unlimited);
                } else {
                    if (m < 0)
                        limit_theta_on_basis_column_for_inf_case_m_neg_lower_bound(
                            j, m, theta, unlimited);
                    else
                        limit_theta_on_basis_column_for_inf_case_m_pos_lower_bound(
                            j, m, theta, unlimited);
                }
                break;
                // case fixed:
                //     if (get_this->current_x_is_feasible()) {
                //         theta = zero_of_type<X>();
                //         break;
                //     }
                //     if (m < 0)
                //         limit_theta_on_basis_column_for_inf_case_m_neg_fixed(j, m,
                //         theta);
                //     else
                //         limit_theta_on_basis_column_for_inf_case_m_pos_fixed(j, m,
                //         theta);
                //     break;
            case column_type::fixed:
            case column_type::boxed:
                if (this->current_x_is_feasible()) {
                    if (m > 0) {
                        limit_theta_on_basis_column_for_feas_case_m_pos_no_check(j, m, theta,
                                                                                 unlimited);
                    } else {
                        limit_theta_on_basis_column_for_feas_case_m_neg_no_check(j, m, theta,
                                                                                 unlimited);
                    }
                } else {
                    if (m > 0) {
                        limit_theta_on_basis_column_for_inf_case_m_pos_boxed(j, m, theta,
                                                                             unlimited);
                    } else {
                        limit_theta_on_basis_column_for_inf_case_m_neg_boxed(j, m, theta,
                                                                             unlimited);
                    }
                }

                break;
            default:
                UNREACHABLE();
        }
        if (!unlimited && theta < zero_of_type<X>()) {
            theta = zero_of_type<X>();
        }
    }
    bool correctly_moved_to_bounds(lpvar) const;
    bool column_is_benefitial_for_entering_basis(unsigned j) const;
    void init_infeasibility_costs();
    void print_column(unsigned j, std::ostream &out);

    void print_bound_info_and_x(unsigned j, std::ostream &out);

    bool basis_column_is_set_correctly(unsigned j) const {
        return this->m_A.m_columns[j].size() == 1;
    }

    bool basis_columns_are_set_correctly() const {
        for (unsigned j : this->m_basis)
            if (!basis_column_is_set_correctly(j))
                return false;

        return this->m_basis_heading.size() == this->m_A.column_count() &&
               this->m_basis.size() == this->m_A.row_count();
    }

    void init_run_tableau();
    void update_x_tableau(unsigned entering, const X &delta);
    // the delta is between the old and the new cost (old - new)
    void update_reduced_cost_for_basic_column_cost_change(const T &delta,
                                                          unsigned j) {
        SASSERT(this->m_basis_heading[j] >= 0);
        unsigned i = static_cast<unsigned>(this->m_basis_heading[j]);
        for (const row_cell<T> &rc : this->m_A.m_rows[i]) {
            unsigned k = rc.var();
            if (k == j)
                continue;
            this->m_d[k] += delta * rc.coeff();
        }
    }

    bool update_basis_and_x_tableau(int entering, int leaving, X const &tt);
    void init_reduced_costs_tableau();
    void init_tableau_rows() {
        m_bland_mode_tableau = false;
        m_left_basis_tableau.reset();
        m_left_basis_repeated = 0;
    }
    // stage1 constructor
    lp_primal_core_solver(
        static_matrix<T, X> &A,
        vector<X> &b,  // the right side vector
        vector<X> &x,  // the number of elements in x needs to be at least as large
                       // as the number of columns in A
        vector<unsigned> &basis, vector<unsigned> &nbasis, std_vector<int> &heading,
        vector<T> &costs, const vector<column_type> &column_type_array,
        const vector<X> &lower_bound_values, const vector<X> &upper_bound_values,
        lp_settings &settings, const column_namer &column_names)
        : lp_core_solver_base<T, X>(A,  // b,
                                    basis, nbasis, heading, x, costs, settings,
                                    column_names, column_type_array,
                                    lower_bound_values, upper_bound_values),
          m_bland_mode_threshold(1000) {
        this->set_status(lp_status::UNKNOWN);
    }

    friend core_solver_pretty_printer<T, X>;
};
}  // namespace lp
