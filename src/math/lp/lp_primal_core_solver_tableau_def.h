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

// this is a part of lp_primal_core_solver that deals with the tableau
#include "math/lp/lp_primal_core_solver.h"
namespace lp {
template <typename T, typename X> void lp_primal_core_solver<T, X>::one_iteration_tableau() {
    int entering = choose_entering_column_tableau();
    if (entering == -1) {
        decide_on_status_when_cannot_find_entering();
    }
    else {
        advance_on_entering_tableau(entering);
    }
    SASSERT(this->inf_heap_is_correct());
}

template <typename T, typename X> void lp_primal_core_solver<T, X>::advance_on_entering_tableau(int entering) {
    X t;
    int leaving = find_leaving_and_t_tableau(entering, t);
    if (leaving == -1) {
        TRACE("lar_solver", tout << "nothing leaving " << entering << "\n";);
        this->set_status(lp_status::UNBOUNDED);
        return;
    }
    advance_on_entering_and_leaving_tableau(entering, leaving, t);
}


 template <typename T, typename X> int lp_primal_core_solver<T, X>::choose_entering_column_tableau() {
    //this moment m_y = cB * B(-1)
    if (this->m_nbasis_sort_counter == 0) {
        sort_non_basis();
        this->m_nbasis_sort_counter = 20;
    }
    else {
        this->m_nbasis_sort_counter--;
    }
    unsigned number_of_benefitial_columns_to_go_over =  get_number_of_non_basic_column_to_try_for_enter();
    
    if (number_of_benefitial_columns_to_go_over == 0)
        return -1;
    
    unsigned j_nz = this->m_m() + 1; // this number is greater than the max column size
    std::list<unsigned>::iterator entering_iter = m_non_basis_list.end();
    unsigned n = 0;
    for (auto non_basis_iter = m_non_basis_list.begin(); number_of_benefitial_columns_to_go_over && non_basis_iter != m_non_basis_list.end(); ++non_basis_iter) {
        unsigned j = *non_basis_iter;
        if (!column_is_benefitial_for_entering_basis(j))
            continue;

        // if we are here then j is a candidate to enter the basis
        unsigned t = this->m_A.number_of_non_zeroes_in_column(j);
        if (t < j_nz) {
            j_nz = t;
            entering_iter = non_basis_iter;
            number_of_benefitial_columns_to_go_over--;
            n = 1;
        }
        else if (t == j_nz && this->m_settings.random_next(++n) == 0) {
            entering_iter = non_basis_iter;
        }
    }
    if (entering_iter == m_non_basis_list.end())
        return -1;
    unsigned entering = *entering_iter;
    m_sign_of_entering_delta = this->m_d[entering] > 0 ? 1 : -1;
    m_non_basis_list.erase(entering_iter);
    m_non_basis_list.push_back(entering);
    return entering;

}

template <typename T, typename X>
unsigned lp_primal_core_solver<T, X>::solve() {
    TRACE("lar_solver", tout << "solve " << this->get_status() << "\n";);
    init_run_tableau();
    if (this->current_x_is_feasible() && this->m_look_for_feasible_solution_only) {
        this->set_status(lp_status::FEASIBLE);
        return 0;
    }
        
    do {
        if (this->m_settings.get_cancel_flag()) {
            this->set_status(lp_status::CANCELLED);
            return this->total_iterations();
        }
        if (this->m_settings.use_tableau_rows()) {
            one_iteration_tableau_rows();
        } else {
            one_iteration_tableau();
        }
        TRACE("lar_solver", tout << "one iteration tableau " << this->get_status() << "\n";);
        switch (this->get_status()) {
        case lp_status::OPTIMAL:  // check again that we are at optimum
            break;
        case lp_status::TENTATIVE_UNBOUNDED:
           UNREACHABLE();
            break;
        case lp_status::UNBOUNDED:
            SASSERT (this->current_x_is_feasible());            
            break;

        case lp_status::UNSTABLE:
           UNREACHABLE();
            break;

        default:
            break; // do nothing
        }
        if (this->m_settings.get_cancel_flag()
            ||
            this->iters_with_no_cost_growing() > this->m_settings.max_number_of_iterations_with_no_improvements
            ) {         
            this->set_status(lp_status::CANCELLED);
            break; // from the loop
        }
    } while (
             this->get_status() != lp_status::UNBOUNDED
             &&
             this->get_status() != lp_status::OPTIMAL
             &&
             this->get_status() != lp_status::INFEASIBLE
             &&
             !(this->current_x_is_feasible() && this->m_look_for_feasible_solution_only)
	);
	
    SASSERT(
              this->get_status() == lp_status::CANCELLED
              ||
              this->current_x_is_feasible() == false
              ||
              this->calc_current_x_is_feasible_include_non_basis());
    return this->total_iterations();

}
template <typename T, typename X>void lp_primal_core_solver<T, X>::advance_on_entering_and_leaving_tableau(int entering, int leaving, X & t) {
    SASSERT(leaving >= 0 && entering >= 0);
    SASSERT((this->m_settings.simplex_strategy() ==
                simplex_strategy_enum::tableau_rows) ||
                m_non_basis_list.back() == static_cast<unsigned>(entering));
    SASSERT(!is_neg(t));
    SASSERT(entering != leaving || !is_zero(t)); // otherwise nothing changes
    if (entering == leaving) {
        advance_on_entering_equal_leaving_tableau(entering, t);
        return;
    }
    if (!is_zero(t)) {
        if (this->current_x_is_feasible() ) {
            if (m_sign_of_entering_delta == -1)
                t = -t;
        }
        this->update_basis_and_x_tableau(entering, leaving, t);
        this->iters_with_no_cost_growing() = 0;
    }
    else {
        this->pivot_column_tableau(entering, this->m_basis_heading[leaving]);
        this->change_basis(entering, leaving);
    }

    if (this->m_look_for_feasible_solution_only && this->current_x_is_feasible())
        return;

    if (this->m_settings.simplex_strategy() != simplex_strategy_enum::tableau_rows) {
        std::list<unsigned>::iterator it = m_non_basis_list.end();
        it--;
        * it = static_cast<unsigned>(leaving);
    }
}

template <typename T, typename X>
void lp_primal_core_solver<T, X>::advance_on_entering_equal_leaving_tableau(int entering, X & t) {
    this->update_x_tableau(entering, t * m_sign_of_entering_delta); 
    if (this->m_look_for_feasible_solution_only && this->current_x_is_feasible())
        return;
    
    
    this->iters_with_no_cost_growing() = 0;
}
template <typename T, typename X> int lp_primal_core_solver<T, X>::find_leaving_and_t_tableau(unsigned entering, X & t) {
    unsigned k = 0;
    bool unlimited = true;
    unsigned row_min_nz = this->m_n() + 1;
    m_leaving_candidates.clear();
    auto & col = this->m_A.m_columns[entering];
    unsigned col_size = static_cast<unsigned>(col.size());
    for (;k < col_size && unlimited; k++) {
        const column_cell & c = col[k];
        unsigned i = c.var();
        const T & ed = this->m_A.get_val(c);
        SASSERT(!numeric_traits<T>::is_zero(ed));
        unsigned j = this->m_basis[i];
        limit_theta_on_basis_column(j, - ed * m_sign_of_entering_delta, t, unlimited);
        if (!unlimited) {
            m_leaving_candidates.push_back(j);
            row_min_nz = static_cast<unsigned>(this->m_A.m_rows[i].size());
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
        unsigned i = c.var();
        const T & ed = this->m_A.get_val(c);
         SASSERT(!numeric_traits<T>::is_zero(ed));
        unsigned j = this->m_basis[i];
        unlimited = true;
        limit_theta_on_basis_column(j, -ed * m_sign_of_entering_delta, ratio, unlimited);
        if (unlimited) continue;
        unsigned i_nz = static_cast<unsigned>(this->m_A.m_rows[i].size());
        if (ratio < t) {
            t = ratio;
            m_leaving_candidates.clear();
            m_leaving_candidates.push_back(j);
            row_min_nz = i_nz;
        } else if (ratio == t && i_nz < row_min_nz) {
            m_leaving_candidates.clear();
            m_leaving_candidates.push_back(j);
            row_min_nz = static_cast<unsigned>(this->m_A.m_rows[i].size());
        } else if (ratio == t && i_nz == row_min_nz) {
            m_leaving_candidates.push_back(j);
        }
    }

    if (try_jump_to_another_bound_on_entering(entering, t)) {
        return entering;
    }
    if (m_leaving_candidates.size() == 1)
        return m_leaving_candidates[0];
    k = this->m_settings.random_next() % m_leaving_candidates.size();
    return m_leaving_candidates[k];
}
template <typename T, typename X> void lp_primal_core_solver<T, X>::init_run_tableau() {
        SASSERT(basis_columns_are_set_correctly());
        this->iters_with_no_cost_growing() = 0;
		SASSERT(this->inf_heap_is_correct());
        if (this->current_x_is_feasible() && this->m_look_for_feasible_solution_only)
            return;
        if (this->m_settings.backup_costs)
            backup_and_normalize_costs();
        
        if (this->m_settings.simplex_strategy() == simplex_strategy_enum::tableau_rows)
            init_tableau_rows();
        SASSERT(this->reduced_costs_are_correct_tableau());
        SASSERT(!this->need_to_pivot_to_basis_tableau());
}

template <typename T, typename X> bool lp_primal_core_solver<T, X>::
update_basis_and_x_tableau(int entering, int leaving, X const & tt) {
    SASSERT(entering != leaving);
    update_x_tableau(entering, tt);
    this->pivot_column_tableau(entering, this->m_basis_heading[leaving]);
    this->change_basis(entering, leaving);
    return true;
}

template <typename T, typename X> void lp_primal_core_solver<T, X>::
update_x_tableau(unsigned entering, const X& delta) {
    this->add_delta_to_x(entering, delta);
    for (const auto & c : this->m_A.m_columns[entering]) {
         unsigned i = c.var();
         this->add_delta_to_x_and_track_feasibility(this->m_basis[i], -  delta * this->m_A.get_val(c));
    }
}


template <typename T, typename X> void lp_primal_core_solver<T, X>::init_reduced_costs_tableau() {
    
    unsigned size = this->m_basis_heading.size();
    for (unsigned j = 0; j < size; j++) {
        if (this->m_basis_heading[j] >= 0)
            this->m_d[j] = zero_of_type<T>();
        else {
            T& d = this->m_d[j] = this->m_costs[j];
            for (auto & cc : this->m_A.m_columns[j]) {
                d -= this->m_costs[this->m_basis[cc.var()]] * this->m_A.get_val(cc);
            }
        }
    }
}
}
