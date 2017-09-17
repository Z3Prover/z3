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
#include <string>
#include "util/vector.h"
#include "util/lp/lp_primal_simplex.h"

namespace lp {
template <typename T, typename X> void lp_primal_simplex<T, X>::fill_costs_and_x_for_first_stage_solver(unsigned original_number_of_columns) {
    unsigned slack_var = original_number_of_columns;
    unsigned artificial = original_number_of_columns + this->m_slacks;

    for (unsigned row = 0; row < this->row_count(); row++) {
        fill_costs_and_x_for_first_stage_solver_for_row(row, slack_var, artificial);
    }
}

template <typename T, typename X> void lp_primal_simplex<T, X>::init_buffer(unsigned k, vector<T> & r) {
    for (unsigned i = 0; i < k; i++) {
        r[i] = 0;
    }
    r[k] = 1;
    for (unsigned i = this->row_count() -1; i > k; i--) {
        r[i] = 0;
    }
}

template <typename T, typename X> void lp_primal_simplex<T, X>::refactor() {
    m_core_solver->init_lu();
    if (m_core_solver->factorization()->get_status() != LU_status::OK) {
        throw_exception("cannot refactor");
    }
}

template <typename T, typename X> void lp_primal_simplex<T, X>::set_scaled_costs() {
    unsigned j = this->number_of_core_structurals();
    while (j-- > 0) {
        this->set_scaled_cost(j);
    }
}

template <typename T, typename X>     column_info<T> * lp_primal_simplex<T, X>::get_or_create_column_info(unsigned column) {
    auto it = this->m_columns.find(column);
    return (it == this->m_columns.end())? ( this->m_columns[column] = new column_info<T>) : it->second;
}

template <typename T, typename X> void lp_primal_simplex<T, X>::fill_acceptable_values_for_x() {
    for (auto t : this->m_core_solver_columns_to_external_columns) {
        this->m_x[t.first] = numeric_traits<T>::zero();
    }
}


template <typename T, typename X> void lp_primal_simplex<T, X>::set_zero_bound(bool * bound_is_set, T * bounds,  unsigned i) {
    bound_is_set[i] = true;
    bounds[i] = numeric_traits<T>::zero();
}

template <typename T, typename X> void lp_primal_simplex<T, X>::fill_costs_and_x_for_first_stage_solver_for_row(
                                                                                                                int row,
                                                                                                                unsigned & slack_var,
                                                                                                                unsigned & artificial) {
    SASSERT(row >= 0 && row < this->row_count());
    auto & constraint = this->m_constraints[this->m_core_solver_rows_to_external_rows[row]];
    // we need to bring the program to the form Ax = b
    T rs = this->m_b[row];
    T artificial_cost =  - numeric_traits<T>::one();
    switch (constraint.m_relation) {
    case Equal: // no slack variable here
        this->m_column_types[artificial] = column_type::low_bound;
        this->m_costs[artificial] = artificial_cost; // we are maximizing, so the artificial, which is non-negatiive, will be pushed to zero
        this->m_basis[row] = artificial;
        if (rs >= 0) {
            (*this->m_A)(row, artificial) = numeric_traits<T>::one();
            this->m_x[artificial] = rs;
        } else {
            (*this->m_A)(row, artificial) = - numeric_traits<T>::one();
            this->m_x[artificial] = - rs;
        }
        artificial++;
        break;

    case Greater_or_equal:
        this->m_column_types[slack_var] = column_type::low_bound;
        (*this->m_A)(row, slack_var) = - numeric_traits<T>::one();

        if (rs > 0) {
            SASSERT(numeric_traits<T>::is_zero(this->m_x[slack_var]));
            // adding one artificial
            this->m_column_types[artificial] = column_type::low_bound;
            (*this->m_A)(row, artificial) = numeric_traits<T>::one();
            this->m_costs[artificial] = artificial_cost;
            this->m_basis[row] = artificial;
            this->m_x[artificial] = rs;
            artificial++;
        } else {
            // we can put a slack_var into the basis, and atemplate <typename T, typename X> void lp_primal_simplex<T, X>::adding an artificial variable
            this->m_basis[row] = slack_var;
            this->m_x[slack_var] = - rs;
        }
        slack_var++;
        break;
    case Less_or_equal:
        // introduce a non-negative slack variable
        this->m_column_types[slack_var] = column_type::low_bound;
        (*this->m_A)(row, slack_var) = numeric_traits<T>::one();

        if (rs < 0) {
            // adding one artificial
            SASSERT(numeric_traits<T>::is_zero(this->m_x[slack_var]));
            this->m_column_types[artificial] = column_type::low_bound;
            (*this->m_A)(row, artificial) = - numeric_traits<T>::one();
            this->m_costs[artificial] = artificial_cost;
            this->m_x[artificial] = - rs;
            this->m_basis[row] = artificial++;
        } else {
            // we can put slack_var into the basis, and atemplate <typename T, typename X> void lp_primal_simplex<T, X>::adding an artificial variable
            this->m_basis[row] = slack_var;
            this->m_x[slack_var] = rs;
        }
        slack_var++;
        break;
    }
}





template <typename T, typename X> void lp_primal_simplex<T, X>::set_core_solver_bounds() {
    unsigned total_vars = this->m_A->column_count() + this->m_slacks + this->m_artificials;
    this->m_column_types.resize(total_vars);
    this->m_upper_bounds.resize(total_vars);
    for (auto cit : this->m_map_from_var_index_to_column_info) {
        column_info<T> * ci = cit.second;
        unsigned j = ci->get_column_index();
        if (!is_valid(j))
            continue; // the variable is not mapped to a column
        switch (this->m_column_types[j] = ci->get_column_type()){
        case column_type::fixed:
            this->m_upper_bounds[j] = numeric_traits<T>::zero();
            break;
        case column_type::boxed:
            this->m_upper_bounds[j] = ci->get_adjusted_upper_bound() / this->m_column_scale[j];
            break;

        default: break; // do nothing
        }
    }
}


template <typename T, typename X> void lp_primal_simplex<T, X>::find_maximal_solution() {
    if (this->problem_is_empty()) {
        this->m_status = lp_status::EMPTY;
        return;
    }

    this->cleanup();
    this->fill_matrix_A_and_init_right_side();
    if (this->m_status == lp_status::INFEASIBLE) {
        return;
    }
    this->m_x.resize(this->m_A->column_count());
    this->fill_m_b();
    this->scale();
    fill_acceptable_values_for_x();
    this->count_slacks_and_artificials();
    set_core_solver_bounds();
    solve_with_total_inf();
}

template <typename T, typename X> void lp_primal_simplex<T, X>::fill_A_x_and_basis_for_stage_one_total_inf() {
    for (unsigned row = 0; row < this->row_count(); row++)
        fill_A_x_and_basis_for_stage_one_total_inf_for_row(row);
}

template <typename T, typename X> void lp_primal_simplex<T, X>::fill_A_x_and_basis_for_stage_one_total_inf_for_row(unsigned row) {
    SASSERT(row < this->row_count());
    auto ext_row_it = this->m_core_solver_rows_to_external_rows.find(row);
    SASSERT(ext_row_it != this->m_core_solver_rows_to_external_rows.end());
    unsigned ext_row = ext_row_it->second;
    auto constr_it = this->m_constraints.find(ext_row);
    SASSERT(constr_it != this->m_constraints.end());
    auto & constraint = constr_it->second;
    unsigned j = this->m_A->column_count(); // j is a slack variable
    this->m_A->add_column();
    // we need to bring the program to the form Ax = b
    this->m_basis[row] = j;
    switch (constraint.m_relation) {
    case Equal:
        this->m_x[j] = this->m_b[row];
        (*this->m_A)(row, j) = numeric_traits<T>::one();
        this->m_column_types[j] = column_type::fixed;
        this->m_upper_bounds[j] = m_low_bounds[j] = zero_of_type<X>();
        break;

    case Greater_or_equal:
        this->m_x[j] = - this->m_b[row];
        (*this->m_A)(row, j) = - numeric_traits<T>::one();
        this->m_column_types[j] = column_type::low_bound;
        this->m_upper_bounds[j] = zero_of_type<X>();
        break;
    case Less_or_equal:
        this->m_x[j] = this->m_b[row];
        (*this->m_A)(row, j) = numeric_traits<T>::one();
        this->m_column_types[j] = column_type::low_bound;
        this->m_upper_bounds[j] = m_low_bounds[j] = zero_of_type<X>();
        break;
    default:
        SASSERT(false);
    }
}

template <typename T, typename X> void lp_primal_simplex<T, X>::solve_with_total_inf() {
    int total_vars = this->m_A->column_count() + this->row_count();
    if (total_vars == 0) {
        this->m_status = OPTIMAL;
        return;
    }
    m_low_bounds.clear();
    m_low_bounds.resize(total_vars, zero_of_type<X>());  // low bounds are shifted ot zero
    this->m_x.resize(total_vars, numeric_traits<T>::zero());
    this->m_basis.resize(this->row_count());
    this->m_costs.clear();
    this->m_costs.resize(total_vars, zero_of_type<T>());
    fill_A_x_and_basis_for_stage_one_total_inf();
    if (this->m_settings.get_message_ostream() != nullptr)
        this->print_statistics_on_A(*this->m_settings.get_message_ostream());
    set_scaled_costs();

    m_core_solver = new lp_primal_core_solver<T, X>(*this->m_A,
                                                    this->m_b,
                                                    this->m_x,
                                                    this->m_basis,
                                                    this->m_nbasis,
                                                    this->m_heading,
                                                    this->m_costs,
                                                    this->m_column_types,
                                                    m_low_bounds,
                                                    this->m_upper_bounds,
                                                    this->m_settings, *this);
    m_core_solver->solve();
    this->set_status(m_core_solver->get_status());
    this->m_total_iterations = m_core_solver->total_iterations();   
}


template <typename T, typename X> lp_primal_simplex<T, X>::~lp_primal_simplex() {
    if (m_core_solver != nullptr) {
        delete m_core_solver;
    }
}

template <typename T, typename X> bool lp_primal_simplex<T, X>::bounds_hold(std::unordered_map<std::string, T> const & solution) {
    for (auto it : this->m_map_from_var_index_to_column_info) {
        auto sol_it = solution.find(it.second->get_name());
        if (sol_it == solution.end()) {
            std::stringstream s;
            s << "cannot find column " << it.first << " in solution";
            throw_exception(s.str() );
        }

        if (!it.second->bounds_hold(sol_it->second)) {
            //            std::cout << "bounds do not hold for " << it.second->get_name() << std::endl;
            it.second->bounds_hold(sol_it->second);
            return false;
        }
    }
    return true;
}

template <typename T, typename X> T lp_primal_simplex<T, X>::get_row_value(unsigned i, std::unordered_map<std::string, T> const & solution, std::ostream * out) {
    auto it = this->m_A_values.find(i);
    if (it == this->m_A_values.end()) {
        std::stringstream s;
        s << "cannot find row " << i;
        throw_exception(s.str() );
    }
    T ret = numeric_traits<T>::zero();
    for (auto & pair : it->second) {
        auto cit = this->m_map_from_var_index_to_column_info.find(pair.first);
        SASSERT(cit != this->m_map_from_var_index_to_column_info.end());
        column_info<T> * ci = cit->second;
        auto sol_it = solution.find(ci->get_name());
        SASSERT(sol_it != solution.end());
        T column_val = sol_it->second;
        if (out != nullptr) {
            (*out) << pair.second << "(" << ci->get_name() << "=" << column_val << ") ";
        }
        ret += pair.second * column_val;
    }
    if (out != nullptr) {
        (*out) << " = " << ret << std::endl;
    }
    return ret;
}

template <typename T, typename X> bool lp_primal_simplex<T, X>::row_constraint_holds(unsigned i, std::unordered_map<std::string, T> const & solution, std::ostream *out) {
    T row_val = get_row_value(i, solution, out);
    auto & constraint = this->m_constraints[i];
    T rs = constraint.m_rs;
    bool print = out != nullptr;
    switch (constraint.m_relation) {
    case Equal:
        if (fabs(numeric_traits<T>::get_double(row_val - rs)) > 0.00001) {
            if (print) {
                (*out) << "should be = " << rs << std::endl;
            }
            return false;
        }
        return true;
    case Greater_or_equal:
        if (numeric_traits<T>::get_double(row_val - rs) < -0.00001) {
            if (print) {
                (*out) << "should be >= " << rs << std::endl;
            }
            return false;
        }
        return true;;

    case Less_or_equal:
        if (numeric_traits<T>::get_double(row_val - rs) > 0.00001) {
            if (print) {
                (*out) << "should be <= " << rs << std::endl;
            }
            return false;
        }
        return true;;
    }
    SASSERT(false);
    return false; // it is unreachable
}

template <typename T, typename X> bool lp_primal_simplex<T, X>::row_constraints_hold(std::unordered_map<std::string, T> const & solution) {
    for (auto it : this->m_A_values) {
        if (!row_constraint_holds(it.first, solution, nullptr)) {
            row_constraint_holds(it.first, solution, nullptr);
            return false;
        }
    }
    return true;
}

template <typename T, typename X> T lp_primal_simplex<T, X>::get_current_cost() const {
    T ret = numeric_traits<T>::zero();
    for (auto it : this->m_map_from_var_index_to_column_info) {
        ret += this->get_column_cost_value(it.first, it.second);
    }
    return ret;
}
}
