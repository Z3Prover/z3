/*
  Copyright (c) 2017 Microsoft Corporation
  Author: Lev Nachmanson
*/

#pragma once
#include <string>
#include <unordered_map>
#include <algorithm>
#include "util/vector.h"
#include "util/lp/lp_settings.h"
#include "util/lp/column_info.h"
#include "util/lp/static_matrix.h"
#include "util/lp/lp_core_solver_base.h"
#include "util/lp/scaler.h"
#include "util/lp/linear_combination_iterator.h"
#include "util/lp/bound_analyzer_on_row.h"
namespace lean {
enum lp_relation  {
    Less_or_equal,
    Equal,
    Greater_or_equal
};

template <typename T, typename X>
struct lp_constraint {
    X m_rs; // right side of the constraint
    lp_relation m_relation;
    lp_constraint() {} // empty constructor
    lp_constraint(T rs, lp_relation relation): m_rs(rs), m_relation(relation) {}
};


template <typename T, typename X>
class lp_solver : public column_namer {
    column_info<T> * get_or_create_column_info(unsigned column);

protected:
    T get_column_cost_value(unsigned j, column_info<T> * ci) const;
public:
    unsigned m_total_iterations;
    static_matrix<T, X>* m_A; // this is the matrix of constraints
    vector<T> m_b; // the right side vector
    unsigned m_first_stage_iterations;
    unsigned m_second_stage_iterations;
    std::unordered_map<unsigned, lp_constraint<T, X>> m_constraints;
    std::unordered_map<var_index, column_info<T>*> m_map_from_var_index_to_column_info;
    std::unordered_map<unsigned, std::unordered_map<unsigned, T> > m_A_values;
    std::unordered_map<std::string, unsigned> m_names_to_columns; // don't have to use it
    std::unordered_map<unsigned, unsigned> m_external_rows_to_core_solver_rows;
    std::unordered_map<unsigned, unsigned> m_core_solver_rows_to_external_rows;
    std::unordered_map<unsigned, unsigned> m_core_solver_columns_to_external_columns;
    vector<T> m_column_scale;
    std::unordered_map<unsigned, std::string>  m_name_map;
    unsigned m_artificials;
    unsigned m_slacks;
    vector<column_type> m_column_types;
    vector<T> m_costs;
    vector<T> m_x;
    vector<T> m_upper_bounds;
    vector<unsigned> m_basis;
    vector<unsigned> m_nbasis;
    vector<int> m_heading;


    lp_status m_status;

    lp_settings m_settings;
    lp_solver():
        m_A(nullptr), // this is the matrix of constraints
        m_first_stage_iterations (0),
        m_second_stage_iterations (0),
        m_artificials (0),
        m_slacks (0),
        m_status(lp_status::UNKNOWN)
    {}

    unsigned row_count() const { return this->m_A->row_count(); }

    void add_constraint(lp_relation relation, T  right_side, unsigned row_index);

    void set_cost_for_column(unsigned column, T  column_cost) {
        get_or_create_column_info(column)->set_cost(column_cost);
    }
    std::string get_column_name(unsigned j) const override;

    void set_row_column_coefficient(unsigned row, unsigned column, T const & val) {
        m_A_values[row][column] = val;
    }
    // returns the current cost
    virtual T get_current_cost() const = 0;
       // do not have to call it
    void give_symbolic_name_to_column(std::string name, unsigned column);

    virtual T get_column_value(unsigned column) const = 0;

    T get_column_value_by_name(std::string name) const;

    // returns -1 if not found
    virtual int get_column_index_by_name(std::string name) const;

    void set_low_bound(unsigned i, T bound) {
        column_info<T> *ci = get_or_create_column_info(i);
        ci->set_low_bound(bound);
    }

    void set_upper_bound(unsigned i, T bound) {
        column_info<T> *ci = get_or_create_column_info(i);
        ci->set_upper_bound(bound);
    }

    void unset_low_bound(unsigned i) {
        get_or_create_column_info(i)->unset_low_bound();
    }

    void unset_upper_bound(unsigned i) {
        get_or_create_column_info(i)->unset_upper_bound();
    }

    void set_fixed_value(unsigned i, T val) {
        column_info<T> *ci = get_or_create_column_info(i);
        ci->set_fixed_value(val);
    }

    void unset_fixed_value(unsigned i) {
        get_or_create_column_info(i)->unset_fixed();
    }

    lp_status get_status() const {
        return m_status;
    }

    void set_status(lp_status st)  {
        m_status = st;
    }

    
    virtual ~lp_solver();

    void flip_costs();

    virtual void find_maximal_solution() = 0;
    void set_time_limit(unsigned time_limit_in_seconds) {
        m_settings.time_limit = time_limit_in_seconds;
    }

    void set_max_iterations_per_stage(unsigned max_iterations) {
        m_settings.max_total_number_of_iterations = max_iterations;
    }

    unsigned get_max_iterations_per_stage() const {
        return m_settings.max_total_number_of_iterations;
    }
protected:
    bool problem_is_empty();

    void scale();


    void print_rows_scale_stats(std::ostream & out);

    void print_columns_scale_stats(std::ostream & out);

    void print_row_scale_stats(unsigned i, std::ostream & out);

    void print_column_scale_stats(unsigned j, std::ostream & out);

    void print_scale_stats(std::ostream & out);

    void get_max_abs_in_row(std::unordered_map<unsigned, T> & row_map);

    void pin_vars_down_on_row(std::unordered_map<unsigned, T> & row) {
        pin_vars_on_row_with_sign(row, - numeric_traits<T>::one());
    }

    void pin_vars_up_on_row(std::unordered_map<unsigned, T> & row) {
        pin_vars_on_row_with_sign(row, numeric_traits<T>::one());
    }

    void pin_vars_on_row_with_sign(std::unordered_map<unsigned, T> & row, T sign );

    bool get_minimal_row_value(std::unordered_map<unsigned, T> & row, T & low_bound);

    bool get_maximal_row_value(std::unordered_map<unsigned, T> & row, T & low_bound);

    bool row_is_zero(std::unordered_map<unsigned, T> & row);

    bool row_e_is_obsolete(std::unordered_map<unsigned, T> & row, unsigned row_index);

    bool row_ge_is_obsolete(std::unordered_map<unsigned, T> & row, unsigned row_index);

    bool row_le_is_obsolete(std::unordered_map<unsigned, T> & row, unsigned row_index);

    // analyse possible max and min values that are derived from var boundaries
    // Let us say that the we have a "ge" constraint, and the min value is equal to the rs.
    // Then we know what values of the variables are. For each positive coeff of the row it has to be
    // the low boundary of the var and for a negative - the upper.

    // this routing also pins the variables to the boundaries
    bool row_is_obsolete(std::unordered_map<unsigned, T> & row, unsigned row_index );

    void remove_fixed_or_zero_columns();

    void remove_fixed_or_zero_columns_from_row(unsigned i, std::unordered_map<unsigned, T> & row);

    unsigned try_to_remove_some_rows();

    void cleanup();

    void map_external_rows_to_core_solver_rows();

    void map_external_columns_to_core_solver_columns();

    unsigned number_of_core_structurals() {
        return static_cast<unsigned>(m_core_solver_columns_to_external_columns.size());
    }

    void restore_column_scales_to_one() {
        for (unsigned i = 0; i < m_column_scale.size(); i++) m_column_scale[i] = numeric_traits<T>::one();
    }

    void unscale();

    void fill_A_from_A_values();

    void fill_matrix_A_and_init_right_side();

    void count_slacks_and_artificials();

    void count_slacks_and_artificials_for_row(unsigned i);

    T low_bound_shift_for_row(unsigned i);

    void fill_m_b();

    T get_column_value_with_core_solver(unsigned column, lp_core_solver_base<T, X> * core_solver) const;
    void set_scaled_cost(unsigned j);
    void print_statistics_on_A(std::ostream & out)  {
        out << "extended A[" << this->m_A->row_count() << "," << this->m_A->column_count() << "]" << std::endl;
    }

public:
    lp_settings & settings() { return m_settings;}
    void print_model(std::ostream & s) const {
        s << "objective = " << get_current_cost() << std::endl;
        s << "column values\n";
        for (auto & it : m_names_to_columns) {
            s << it.first << " = " << get_column_value(it.second) << std::endl;
        }
    }
};
}
