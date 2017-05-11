/*
  Copyright (c) 2017 Microsoft Corporation
  Author: Lev Nachmanson
*/
// this is a part of lp_primal_core_solver that deals with the tableau
#include "util/lp/lp_primal_core_solver.h"
namespace lean {
template <typename T, typename X> void lp_primal_core_solver<T, X>::one_iteration_tableau() {
    int entering = choose_entering_column_tableau();
    if (entering == -1) {
        decide_on_status_when_cannot_find_entering();
    }
    else {
        advance_on_entering_tableau(entering);
    }
    lean_assert(this->inf_set_is_correct());
}

template <typename T, typename X> void lp_primal_core_solver<T, X>::advance_on_entering_tableau(int entering) {
    X t;
    int leaving = find_leaving_and_t_tableau(entering, t);
    if (leaving == -1) {
        this->set_status(UNBOUNDED);
        return;
    }
    advance_on_entering_and_leaving_tableau(entering, leaving, t);
}
/*
template <typename T, typename X> int lp_primal_core_solver<T, X>::choose_entering_column_tableau_rows() {
    int i = find_inf_row();
    if (i == -1)
        return -1;
    return find_shortest_beneficial_column_in_row(i);
 }
*/
 template <typename T, typename X> int lp_primal_core_solver<T, X>::choose_entering_column_tableau() {
    //this moment m_y = cB * B(-1)
    unsigned number_of_benefitial_columns_to_go_over =  get_number_of_non_basic_column_to_try_for_enter();
    
    lean_assert(numeric_traits<T>::precise());
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
        unsigned t = this->m_A.number_of_non_zeroes_in_column(j);
        if (t < j_nz) {
            j_nz = t;
            entering_iter = non_basis_iter;
            if (number_of_benefitial_columns_to_go_over)
                number_of_benefitial_columns_to_go_over--;
        }
        else if (t == j_nz && this->m_settings.random_next() % 2 == 0) {
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
unsigned lp_primal_core_solver<T, X>::solve_with_tableau() {
    init_run_tableau();
    if (this->current_x_is_feasible() && this->m_look_for_feasible_solution_only) {
        this->set_status(FEASIBLE);
        return 0;
    }
        
    if ((!numeric_traits<T>::precise()) && this->A_mult_x_is_off()) {
        this->set_status(FLOATING_POINT_ERROR);
        return 0;
    }
    do {
        if (this->print_statistics_with_iterations_and_nonzeroes_and_cost_and_check_that_the_time_is_over((this->m_using_infeas_costs? "inf t" : "feas t"), * this->m_settings.get_message_ostream())) {
            return this->total_iterations();
        }
        if (this->m_settings.use_tableau_rows())
            one_iteration_tableau_rows();
        else 
            one_iteration_tableau();
        switch (this->get_status()) {
        case OPTIMAL:  // double check that we are at optimum
        case INFEASIBLE:
            if (this->m_look_for_feasible_solution_only && this->current_x_is_feasible())
                break;
            if (!numeric_traits<T>::precise()) {
                if(this->m_look_for_feasible_solution_only)
                    break;
                this->init_lu();
                
                if (this->m_factorization->get_status() != LU_status::OK) {
                    this->set_status(FLOATING_POINT_ERROR);
                    break;
                }
                init_reduced_costs();
                if (choose_entering_column(1) == -1) {
                    decide_on_status_when_cannot_find_entering();
                    break;
                }
                this->set_status(UNKNOWN);
            } else { // precise case
                if ((!this->infeasibility_costs_are_correct())) {
                    init_reduced_costs_tableau(); // forcing recalc
                    if (choose_entering_column_tableau() == -1) {
                        decide_on_status_when_cannot_find_entering();
                        break;
                    }
                    this->set_status(UNKNOWN);
                }
            }
            break;
        case TENTATIVE_UNBOUNDED:
            this->init_lu();
            if (this->m_factorization->get_status() != LU_status::OK) {
                this->set_status(FLOATING_POINT_ERROR);
                break;
            }
                
            init_reduced_costs();
            break;
        case UNBOUNDED:
            if (this->current_x_is_infeasible()) {
                init_reduced_costs();
                this->set_status(UNKNOWN);
            }
            break;

        case UNSTABLE:
            lean_assert(! (numeric_traits<T>::precise()));
            this->init_lu();
            if (this->m_factorization->get_status() != LU_status::OK) {
                this->set_status(FLOATING_POINT_ERROR);
                break;
            }
            init_reduced_costs();
            break;

        default:
            break; // do nothing
        }
    } while (this->get_status() != FLOATING_POINT_ERROR
             &&
             this->get_status() != UNBOUNDED
             &&
             this->get_status() != OPTIMAL
             &&
             this->get_status() != INFEASIBLE
             &&
             this->iters_with_no_cost_growing() <= this->m_settings.max_number_of_iterations_with_no_improvements
             &&
             this->total_iterations() <= this->m_settings.max_total_number_of_iterations
             &&
             !(this->current_x_is_feasible() && this->m_look_for_feasible_solution_only));

    lean_assert(this->get_status() == FLOATING_POINT_ERROR
                ||
                this->current_x_is_feasible() == false
                ||
                this->calc_current_x_is_feasible_include_non_basis());
    return this->total_iterations();

}
template <typename T, typename X>void lp_primal_core_solver<T, X>::advance_on_entering_and_leaving_tableau(int entering, int leaving, X & t) {
    lean_assert(this->A_mult_x_is_off() == false);
    lean_assert(leaving >= 0 && entering >= 0);
    lean_assert((this->m_settings.simplex_strategy() ==
                simplex_strategy_enum::tableau_rows) ||
                m_non_basis_list.back() == static_cast<unsigned>(entering));
    lean_assert(this->m_using_infeas_costs || !is_neg(t));
    lean_assert(entering != leaving || !is_zero(t)); // otherwise nothing changes
    if (entering == leaving) {
        advance_on_entering_equal_leaving_tableau(entering, t);
        return;
    }
    if (!is_zero(t)) {
        if (this->current_x_is_feasible() || !this->m_settings.use_breakpoints_in_feasibility_search ) {
            if (m_sign_of_entering_delta == -1)
                t = -t;
        }
        this->update_basis_and_x_tableau(entering, leaving, t);
        lean_assert(this->A_mult_x_is_off() == false);
        this->iters_with_no_cost_growing() = 0;
    } else {
        this->pivot_column_tableau(entering, this->m_basis_heading[leaving]);
        this->change_basis(entering, leaving);
    }

    if (this->m_look_for_feasible_solution_only && this->current_x_is_feasible())
        return;

    if (this->m_settings.simplex_strategy() != simplex_strategy_enum::tableau_rows) {
        if (need_to_switch_costs()) {
            this->init_reduced_costs_tableau();
        }
        
        lean_assert(!need_to_switch_costs());
        std::list<unsigned>::iterator it = m_non_basis_list.end();
        it--;
        * it = static_cast<unsigned>(leaving);
    }
}

template <typename T, typename X>
void lp_primal_core_solver<T, X>::advance_on_entering_equal_leaving_tableau(int entering, X & t) {
    lean_assert(!this->A_mult_x_is_off() );
    this->update_x_tableau(entering, t * m_sign_of_entering_delta); 
    if (this->m_look_for_feasible_solution_only && this->current_x_is_feasible())
        return;
    
    if (need_to_switch_costs()) {
        init_reduced_costs_tableau();
    }
    this->iters_with_no_cost_growing() = 0;
}
template <typename T, typename X> int lp_primal_core_solver<T, X>::find_leaving_and_t_tableau(unsigned entering, X & t) {
    unsigned k = 0;
    bool unlimited = true;
    unsigned row_min_nz = this->m_n() + 1;
    m_leaving_candidates.clear();
    auto & col = this->m_A.m_columns[entering];
    unsigned col_size = col.size();
    for (;k < col_size && unlimited; k++) {
        const column_cell & c = col[k];
        unsigned i = c.m_i;
        const T & ed = this->m_A.get_val(c);
        lean_assert(!numeric_traits<T>::is_zero(ed));
        unsigned j = this->m_basis[i];
        limit_theta_on_basis_column(j, - ed * m_sign_of_entering_delta, t, unlimited);
        if (!unlimited) {
            m_leaving_candidates.push_back(j);
            row_min_nz = this->m_A.m_rows[i].size();
        }
    }
    if (unlimited) {
        if (try_jump_to_another_bound_on_entering_unlimited(entering, t))
            return entering;
        return -1;
    }

    X ratio;
    for (;k < col_size; k++) {
        const column_cell & c = col[k];
        unsigned i = c.m_i;
        const T & ed = this->m_A.get_val(c);
         lean_assert(!numeric_traits<T>::is_zero(ed));
        unsigned j = this->m_basis[i];
        unlimited = true;
        limit_theta_on_basis_column(j, -ed * m_sign_of_entering_delta, ratio, unlimited);
        if (unlimited) continue;
        unsigned i_nz = this->m_A.m_rows[i].size();
        if (ratio < t) {
            t = ratio;
            m_leaving_candidates.clear();
            m_leaving_candidates.push_back(j);
            row_min_nz = i_nz;
        } else if (ratio == t && i_nz < row_min_nz) {
            m_leaving_candidates.clear();
            m_leaving_candidates.push_back(j);
            row_min_nz = this->m_A.m_rows[i].size();
        } else if (ratio == t && i_nz == row_min_nz) {
            m_leaving_candidates.push_back(j);
        }
    }

    ratio = t;
    unlimited = false;
    if (try_jump_to_another_bound_on_entering(entering, t, ratio, unlimited)) {
        t = ratio;
        return entering;
    }
    if (m_leaving_candidates.size() == 1)
        return m_leaving_candidates[0];
    k = this->m_settings.random_next() % m_leaving_candidates.size();
    return m_leaving_candidates[k];
}
template <typename T, typename X> void lp_primal_core_solver<T, X>::init_run_tableau() {
        //        print_matrix(&(this->m_A), std::cout);
        lean_assert(this->A_mult_x_is_off() == false);
        lean_assert(basis_columns_are_set_correctly());
        this->m_basis_sort_counter = 0; // to initiate the sort of the basis
        this->set_total_iterations(0);
        this->iters_with_no_cost_growing() = 0;
		lean_assert(this->inf_set_is_correct());
        if (this->current_x_is_feasible() && this->m_look_for_feasible_solution_only)
            return;
        if (this->m_settings.backup_costs)
            backup_and_normalize_costs();
        m_epsilon_of_reduced_cost = numeric_traits<X>::precise() ? zero_of_type<T>() : T(1) / T(10000000);
        if (this->m_settings.use_breakpoints_in_feasibility_search)
            m_breakpoint_indices_queue.resize(this->m_n());
        if (!numeric_traits<X>::precise()) {
            this->m_column_norm_update_counter = 0;
            init_column_norms();
        }
        if (this->m_settings.simplex_strategy() == simplex_strategy_enum::tableau_rows)
            init_tableau_rows();
        lean_assert(this->reduced_costs_are_correct_tableau());
        lean_assert(!this->need_to_pivot_to_basis_tableau());
}

template <typename T, typename X> bool lp_primal_core_solver<T, X>::
update_basis_and_x_tableau(int entering, int leaving, X const & tt) {
    lean_assert(this->use_tableau());
    update_x_tableau(entering, tt);
    this->pivot_column_tableau(entering, this->m_basis_heading[leaving]);
    this->change_basis(entering, leaving);
    return true;
}
template <typename T, typename X> void lp_primal_core_solver<T, X>::
update_x_tableau(unsigned entering, const X& delta) {
    if (!this->m_using_infeas_costs) {
        this->m_x[entering] += delta;
        for (const auto & c : this->m_A.m_columns[entering]) {
            unsigned i = c.m_i;
            this->m_x[this->m_basis[i]] -= delta * this->m_A.get_val(c);
            this->update_column_in_inf_set(this->m_basis[i]);
        }
    } else { // m_using_infeas_costs == true
        this->m_x[entering] += delta;
        lean_assert(this->column_is_feasible(entering));
        lean_assert(this->m_costs[entering] == zero_of_type<T>());
        // m_d[entering] can change because of the cost change for basic columns.
        for (const auto & c : this->m_A.m_columns[entering]) {
            unsigned i = c.m_i;
            unsigned j = this->m_basis[i];
            this->m_x[j] -= delta * this->m_A.get_val(c);
            update_inf_cost_for_column_tableau(j);
            if (is_zero(this->m_costs[j]))
                this->m_inf_set.erase(j);
            else
                this->m_inf_set.insert(j);
        }
    }
    lean_assert(this->A_mult_x_is_off() == false);
}

template <typename T, typename X> void lp_primal_core_solver<T, X>::
update_inf_cost_for_column_tableau(unsigned j) {
    lean_assert(this->m_settings.simplex_strategy() != simplex_strategy_enum::tableau_rows);
    lean_assert(this->m_using_infeas_costs);
    T new_cost = get_infeasibility_cost_for_column(j);
    T delta = this->m_costs[j] - new_cost;
    if (is_zero(delta))
        return;
    this->m_costs[j] = new_cost;
    update_reduced_cost_for_basic_column_cost_change(delta, j);
}

template <typename T, typename X> void lp_primal_core_solver<T, X>::init_reduced_costs_tableau() {
    if (this->current_x_is_infeasible() && !this->m_using_infeas_costs) {
        init_infeasibility_costs();
    } else if (this->current_x_is_feasible() && this->m_using_infeas_costs) {
        if (this->m_look_for_feasible_solution_only)
            return;
        this->m_costs = m_costs_backup;
        this->m_using_infeas_costs = false;
    }
    unsigned size = this->m_basis_heading.size();
    for (unsigned j = 0; j < size; j++) {
        if (this->m_basis_heading[j] >= 0)
            this->m_d[j] = zero_of_type<T>();
        else {
            T& d = this->m_d[j] = this->m_costs[j];
            for (auto & cc : this->m_A.m_columns[j]) {
                d -= this->m_costs[this->m_basis[cc.m_i]] * this->m_A.get_val(cc);
            }
        }
    }
}
}
