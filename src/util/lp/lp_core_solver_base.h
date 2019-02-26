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
#include <set>
#include "util/vector.h"
#include <string>
#include "util/lp/lp_utils.h"
#include "util/lp/core_solver_pretty_printer.h"
#include "util/lp/numeric_pair.h"
#include "util/lp/static_matrix.h"
#include "util/lp/lu.h"
#include "util/lp/permutation_matrix.h"
#include "util/lp/column_namer.h"

namespace lp {

template <typename T, typename X> // X represents the type of the x variable and the bounds
class lp_core_solver_base {    
    unsigned m_total_iterations;
    unsigned m_iters_with_no_cost_growing;
    unsigned inc_total_iterations() { ++m_settings.st().m_total_iterations; return m_total_iterations++; }
private:
    lp_status m_status;
public:
    bool current_x_is_feasible() const {
        TRACE("feas",
              if (m_inf_set.size()) {
                  tout << "column " << m_inf_set.m_index[0] << " is infeasible" << std::endl;
                  print_column_info(m_inf_set.m_index[0], tout);
              } else {
                  tout << "x is feasible\n";
              }
              );
        return m_inf_set.size() == 0;
    }
    bool current_x_is_infeasible() const { return m_inf_set.size() != 0; }
    int_set m_inf_set;
    bool m_using_infeas_costs;


    vector<unsigned>      m_columns_nz; // m_columns_nz[i] keeps an approximate value of non zeroes the i-th column
    vector<unsigned>      m_rows_nz; // m_rows_nz[i] keeps an approximate value of non zeroes in the i-th row
    indexed_vector<T>     m_pivot_row_of_B_1;  // the pivot row of the reverse of B
    indexed_vector<T>     m_pivot_row; // this is the real pivot row of the simplex tableu
    static_matrix<T, X> & m_A; // the matrix A
    vector<X> &           m_b; // the right side
    vector<unsigned> &    m_basis;
    vector<unsigned>&     m_nbasis;
    vector<int>&          m_basis_heading;
    vector<X> &           m_x; // a feasible solution, the fist time set in the constructor
    vector<T> &           m_costs;
    lp_settings &         m_settings;
    vector<T>             m_y; // the buffer for yB = cb
    // a device that is able to solve Bx=c, xB=d, and change the basis
    lu<static_matrix<T, X>> *            m_factorization;
    const column_namer &  m_column_names;
    indexed_vector<T>     m_w; // the vector featuring in 24.3 of the Chvatal book
    vector<T>             m_d; // the vector of reduced costs
    indexed_vector<T>     m_ed; // the solution of B*m_ed = a
    const vector<column_type> & m_column_types;
    const vector<X> &     m_lower_bounds;
    const vector<X> &     m_upper_bounds;
    vector<T>             m_column_norms; // the approximate squares of column norms that help choosing a profitable column
    vector<X>             m_copy_of_xB;
    unsigned              m_basis_sort_counter;
    vector<T>             m_steepest_edge_coefficients;
    vector<unsigned>      m_trace_of_basis_change_vector; // the even positions are entering, the odd positions are leaving
    bool                  m_tracing_basis_changes;
    int_set*              m_pivoted_rows;
    bool                  m_look_for_feasible_solution_only;

    void start_tracing_basis_changes() {
        m_trace_of_basis_change_vector.resize(0);
        m_tracing_basis_changes = true;
    }
        
    void stop_tracing_basis_changes() {
        m_tracing_basis_changes = false;
    }

    void trace_basis_change(unsigned entering, unsigned leaving) {
        unsigned size = m_trace_of_basis_change_vector.size();
        if (size >= 2 && m_trace_of_basis_change_vector[size-2] == leaving
                &&  m_trace_of_basis_change_vector[size -1] == entering) {
            m_trace_of_basis_change_vector.pop_back();
            m_trace_of_basis_change_vector.pop_back();
        } else {
            m_trace_of_basis_change_vector.push_back(entering);
            m_trace_of_basis_change_vector.push_back(leaving);
        }
    }
    
    unsigned m_m() const { return m_A.row_count(); } // it is the length of basis. The matrix m_A has m_m rows and the dimension of the matrix A is m_m
    unsigned m_n() const { return m_A.column_count(); } // the number of columns in the matrix m_A

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
                        const vector<X> & lower_bound_values,
                        const vector<X> & upper_bound_values);

    void allocate_basis_heading();
    void init();

    virtual ~lp_core_solver_base() {
        if (m_factorization != nullptr)
            delete m_factorization;
     }

    vector<unsigned> & non_basis() {
        return m_nbasis;
    }

    const vector<unsigned> & non_basis() const { return m_nbasis; }


    
    void set_status(lp_status status) {
        m_status = status;
    }
    lp_status get_status() const{
        return m_status;
    }

    void fill_cb(T * y);

    void fill_cb(vector<T> & y);

    void solve_yB(vector<T> & y);

    void solve_Bd(unsigned entering);

    void solve_Bd(unsigned entering, indexed_vector<T> & column);

    void pretty_print(std::ostream & out);

    void save_state(T * w_buffer, T * d_buffer);

    void restore_state(T * w_buffer, T * d_buffer);

    X get_cost() {
        return dot_product(m_costs, m_x);
    }

    void copy_m_w(T * buffer);

    void restore_m_w(T * buffer);

    // needed for debugging
    void copy_m_ed(T * buffer);

    void restore_m_ed(T * buffer);

    bool A_mult_x_is_off() const;

    bool A_mult_x_is_off_on_index(const vector<unsigned> & index) const;
    // from page 182 of Istvan Maros's book
    void calculate_pivot_row_of_B_1(unsigned pivot_row);

    void calculate_pivot_row_when_pivot_row_of_B1_is_ready(unsigned pivot_row);

    void update_x(unsigned entering, const X & delta);

    const T & get_var_value(unsigned j) const {
        return m_x[j];
    }

    void print_statistics(char const* str, X cost, std::ostream & message_stream);

    bool print_statistics_with_iterations_and_check_that_the_time_is_over(std::ostream & message_stream);

    bool print_statistics_with_iterations_and_nonzeroes_and_cost_and_check_that_the_time_is_over(char const* str, std::ostream & message_stream);

    bool print_statistics_with_cost_and_check_that_the_time_is_over(X cost, std::ostream & message_stream);

    unsigned total_iterations() const { return m_total_iterations; }

    void set_total_iterations(unsigned s) { m_total_iterations = s; }

    void set_non_basic_x_to_correct_bounds();

    bool at_bound(const X &x, const X & bound) const {
        return !below_bound(x, bound) && !above_bound(x, bound);
    }


    bool need_to_pivot_to_basis_tableau() const {
        unsigned m = m_A.row_count();
        for (unsigned i = 0; i < m; i++) {
            unsigned bj = m_basis[i];
            lp_assert(m_A.m_columns[bj].size() > 0);
            if (m_A.m_columns[bj].size() > 1)
                return true;
            for (const auto & c : m_A.m_columns[bj]) {
                if (m_A.get_val(c) != one_of_type<mpq>())
                    return true;
                else
                    break;
            }
        }
        return false;
    }
    
    bool reduced_costs_are_correct_tableau() const {
        if (m_settings.simplex_strategy() == simplex_strategy_enum::tableau_rows)
            return true;
        CASSERT("check_static_matrix", m_A.is_correct());
        if (m_using_infeas_costs) {
            if (infeasibility_costs_are_correct() == false) {
                return false;
            }
        }
            
        unsigned n = m_A.column_count();
        for (unsigned j = 0; j < n; j++) {
            if (m_basis_heading[j] >= 0) {
                if (!is_zero(m_d[j])) {
                    return false;
                }
            } else {
                auto d = m_costs[j];
                for (const auto & cc : this->m_A.m_columns[j]) {
                    d -= this->m_costs[this->m_basis[cc.var()]] * this->m_A.get_val(cc);
                }
                if (m_d[j] != d) {
                    return false;
                }
            }
        }
        return true;
    }
    
    bool below_bound(const X & x, const X & bound) const {
        if (precise()) return x < bound;
        return below_bound_numeric<X>(x, bound, m_settings.primal_feasibility_tolerance);
    }

    bool above_bound(const X & x, const X & bound) const {
        if (precise()) return x > bound;
        return above_bound_numeric<X>(x, bound, m_settings.primal_feasibility_tolerance);
    }

    bool x_below_low_bound(unsigned p) const {
        return below_bound(m_x[p], m_lower_bounds[p]);
    }

    bool infeasibility_costs_are_correct() const;
    bool infeasibility_cost_is_correct_for_column(unsigned j) const;
    
    bool x_above_lower_bound(unsigned p) const {
        return above_bound(m_x[p], m_lower_bounds[p]);
    }

    bool x_below_upper_bound(unsigned p) const {
        return below_bound(m_x[p], m_upper_bounds[p]);
    }


    bool x_above_upper_bound(unsigned p) const {
        return above_bound(m_x[p], m_upper_bounds[p]);
    }
    bool x_is_at_lower_bound(unsigned j) const {
        return at_bound(m_x[j], m_lower_bounds[j]);
    }
    bool x_is_at_upper_bound(unsigned j) const {
        return at_bound(m_x[j], m_upper_bounds[j]);
    }

    bool x_is_at_bound(unsigned j) const {
        return x_is_at_lower_bound(j) || x_is_at_upper_bound(j);
    }
    bool column_is_feasible(unsigned j) const;

    bool calc_current_x_is_feasible_include_non_basis() const;

    bool inf_set_is_correct() const;
    
    bool column_is_dual_feasible(unsigned j) const;

    bool d_is_not_negative(unsigned j) const;

    bool d_is_not_positive(unsigned j) const;


    bool time_is_over();

    void rs_minus_Anx(vector<X> & rs);

    bool find_x_by_solving();

    bool update_basis_and_x(int entering, int leaving, X const & tt);

    bool basis_has_no_doubles() const;

    bool non_basis_has_no_doubles() const;

    bool basis_is_correctly_represented_in_heading() const ;
    bool non_basis_is_correctly_represented_in_heading() const ;

    bool basis_heading_is_correct() const;

    void restore_x_and_refactor(int entering, int leaving, X const & t);

    void restore_x(unsigned entering, X const & t);

    void fill_reduced_costs_from_m_y_by_rows();

    void copy_rs_to_xB(vector<X> & rs);
    virtual bool lower_bounds_are_set() const { return false; }
    X lower_bound_value(unsigned j) const { return m_lower_bounds[j]; }
    X upper_bound_value(unsigned j) const { return m_upper_bounds[j]; }

    column_type get_column_type(unsigned j) const {return m_column_types[j]; }

    bool pivot_row_element_is_too_small_for_ratio_test(unsigned j) {
        return m_settings.abs_val_is_smaller_than_pivot_tolerance(m_pivot_row[j]);
    }

    X bound_span(unsigned j) const {
        return m_upper_bounds[j] - m_lower_bounds[j];
    }

    std::string column_name(unsigned column) const;

    void copy_right_side(vector<X> & rs);

    void add_delta_to_xB(vector<X> & del);

    void find_error_in_BxB(vector<X>& rs);

    // recalculates the projection of x to B, such that Ax = b, whereab is the right side
    void solve_Ax_eq_b();

    bool snap_non_basic_x_to_bound() {
        bool ret = false;
        for (unsigned j : non_basis())
            ret = snap_column_to_bound(j) || ret;
        return ret;
    }

    
    
    bool snap_column_to_bound(unsigned j) {
        switch (m_column_types[j]) {
        case column_type::fixed:
            if (x_is_at_bound(j))
                break;
            m_x[j] = m_lower_bounds[j];
            return true;
        case column_type::boxed:
            if (x_is_at_bound(j))
                break; // we should preserve x if possible
            // snap randomly
            if (m_settings.random_next() % 2 == 1) 
                m_x[j] = m_lower_bounds[j];
            else
                m_x[j] = m_upper_bounds[j];
            return true;
        case column_type::lower_bound:
            if (x_is_at_lower_bound(j))
                break;
            m_x[j] = m_lower_bounds[j];
            return true;
        case column_type::upper_bound:
            if (x_is_at_upper_bound(j))
                break;
            m_x[j] = m_upper_bounds[j];
            return true;
        default:
            break;
        }
        return false;
    }

    bool make_column_feasible(unsigned j, numeric_pair<mpq> & delta) {
        bool ret = false;
        lp_assert(m_basis_heading[j] < 0);
        auto & x = m_x[j];
        switch (m_column_types[j]) {
        case column_type::fixed:
            lp_assert(m_lower_bounds[j] == m_upper_bounds[j]);
            if (x != m_lower_bounds[j]) {
                delta = m_lower_bounds[j] - x;
                ret = true;;
            }
            break;
        case column_type::boxed:
            if (x < m_lower_bounds[j]) {
                delta = m_lower_bounds[j] - x;
                ret = true;;
            }
            if (x > m_upper_bounds[j]) {
                delta = m_upper_bounds[j] - x;
                ret = true;
            }
            break;
        case column_type::lower_bound:
            if (x < m_lower_bounds[j]) {
                delta = m_lower_bounds[j] - x;
                ret = true;
            }
            break;
        case column_type::upper_bound:
            if (x > m_upper_bounds[j]) {
                delta = m_upper_bounds[j] - x;
                ret = true;
            }
            break;
        default:
            break;
        }
        if (ret)
            add_delta_to_x_and_call_tracker(j, delta);

        return ret;
        
    }

    
    void snap_non_basic_x_to_bound_and_free_to_zeroes();
    void snap_xN_to_bounds_and_fill_xB();

    void snap_xN_to_bounds_and_free_columns_to_zeroes();

    void init_reduced_costs_for_one_iteration();

    non_basic_column_value_position get_non_basic_column_value_position(unsigned j) const;

    void init_lu();
    int pivots_in_column_and_row_are_different(int entering, int leaving) const;
    void pivot_fixed_vars_from_basis();
    bool remove_from_basis(unsigned j);
    bool pivot_column_general(unsigned j, unsigned j_basic, indexed_vector<T> & w);
    bool pivot_for_tableau_on_basis();
    bool pivot_row_for_tableau_on_basis(unsigned row);
    void init_basic_part_of_basis_heading() {
        unsigned m = m_basis.size();
        for (unsigned i = 0; i < m; i++) {
            unsigned column = m_basis[i];
            m_basis_heading[column] = i;
        }
    }

    void init_non_basic_part_of_basis_heading() {
        this->m_nbasis.clear();
        for (int j = m_basis_heading.size(); j--;){
            if (m_basis_heading[j] < 0) {
                m_nbasis.push_back(j);
                // the index of column j in m_nbasis is (- basis_heading[j] - 1)
                m_basis_heading[j] = - static_cast<int>(m_nbasis.size());
            }
        }
    }
    
    void init_basis_heading_and_non_basic_columns_vector() {
        m_basis_heading.resize(0);
        m_basis_heading.resize(m_n(), -1);
        init_basic_part_of_basis_heading();
        init_non_basic_part_of_basis_heading();
    }

    void change_basis_unconditionally(unsigned entering, unsigned leaving) {
        lp_assert(m_basis_heading[entering] < 0);
        int place_in_non_basis = -1 - m_basis_heading[entering];
        if (static_cast<unsigned>(place_in_non_basis) >= m_nbasis.size()) {
              // entering variable in not in m_nbasis, we need to put it back;
            m_basis_heading[entering] = place_in_non_basis = m_nbasis.size();
            m_nbasis.push_back(entering);
        }
        
        int place_in_basis =  m_basis_heading[leaving];
        m_basis_heading[entering] = place_in_basis;
        m_basis[place_in_basis] = entering;
        m_basis_heading[leaving] = -place_in_non_basis - 1;
        m_nbasis[place_in_non_basis] = leaving;
        if (m_tracing_basis_changes)
            trace_basis_change(entering, leaving);
        
    }
    
    void change_basis(unsigned entering, unsigned leaving) {
        lp_assert(m_basis_heading[entering] < 0);
		lp_assert(m_basis_heading[leaving] >= 0);
        
        int place_in_basis =  m_basis_heading[leaving];
        int place_in_non_basis = - m_basis_heading[entering] - 1;
        m_basis_heading[entering] = place_in_basis;
        m_basis[place_in_basis] = entering;

        m_basis_heading[leaving] = -place_in_non_basis - 1;
        m_nbasis[place_in_non_basis] = leaving;
        
        if (m_tracing_basis_changes)
            trace_basis_change(entering, leaving);
    }

    void restore_basis_change(unsigned entering, unsigned leaving) {
        if (m_basis_heading[entering] < 0) {
            return; // the basis has not been changed
        }
        change_basis_unconditionally(leaving, entering);
    }

    bool non_basic_column_is_set_correctly(unsigned j) const {
        if (j >= this->m_n())
            return false;
        switch (this->m_column_types[j]) {
        case column_type::fixed:
        case column_type::boxed:
            if (!this->x_is_at_bound(j))
                return false;
            break;
        case column_type::lower_bound:
            if (!this->x_is_at_lower_bound(j))
                return false;
            break;
        case column_type::upper_bound:
            if (!this->x_is_at_upper_bound(j))
                return false;
            break;
        case column_type::free_column:
            break;
        default:
            lp_assert(false);
            break;
        }
        return true;
    }
    bool non_basic_columns_are_set_correctly() const {
        for (unsigned j : this->m_nbasis)
            if (!column_is_feasible(j)) {
                return false;
            }
        return true;
    }

    void print_column_bound_info(unsigned j, std::ostream & out) const {
        out << column_name(j) << " type = " << column_type_to_string(m_column_types[j]) << std::endl;
        switch (m_column_types[j]) {
        case column_type::fixed:
        case column_type::boxed:
            out << "(" << m_lower_bounds[j] << ", " << m_upper_bounds[j] << ")" << std::endl;
            break;
        case column_type::lower_bound:
            out << m_lower_bounds[j] << std::endl;
            break;
        case column_type::upper_bound:
            out << m_upper_bounds[j] << std::endl;
            break;
        default:
            break;
        }
    }

    void print_column_info(unsigned j, std::ostream & out) const {
        out << "j = " << j << ",\tname = "<< column_name(j) << "\t";
        switch (m_column_types[j]) {
        case column_type::fixed:
        case column_type::boxed:
            out << " [" << m_lower_bounds[j] << ", " << m_upper_bounds[j] << "]";
            break;
        case column_type::lower_bound:
            out << " [" << m_lower_bounds[j] << "," << "oo" << "]";
            break;
        case column_type::upper_bound:
            out << " [-oo, " << m_upper_bounds[j] << ']';
            break;
        case column_type::free_column:
            out << " [-oo, oo]";
            break;
        default:
            lp_assert(false);
        }
        //        out << "basis heading = " << m_basis_heading[j] << std::endl;
        out << "\tx = " << m_x[j];
        if (m_basis_heading[j] >= 0)
            out << " base\n";
        else
           out << " \n";
    }

    bool column_is_free(unsigned j) const { return this->m_column_type[j] == free; }

    bool column_has_upper_bound(unsigned j) const {
        switch(m_column_types[j]) {
        case column_type::free_column:
        case column_type::lower_bound:
            return false;
        default:
            return true;
        }
    }

    bool bounds_for_boxed_are_set_correctly() const {
        for (unsigned j = 0; j < m_column_types.size(); j++) {
            if (m_column_types[j] != column_type::boxed) continue;
            if (m_lower_bounds[j] > m_upper_bounds[j])
                return false;
        }
        return true;
    }
    
    bool column_has_lower_bound(unsigned j) const {
        switch(m_column_types[j]) {
        case column_type::free_column:
        case column_type::upper_bound:
            return false;
        default:
            return true;
        }
    }

    // only check for basic columns
    bool calc_current_x_is_feasible() const {
        unsigned i = this->m_m();
        while (i--) {
            if (!column_is_feasible(m_basis[i]))
                return false;
        }
        return true;
    }

    void transpose_rows_tableau(unsigned i, unsigned ii);
    
    void pivot_to_reduced_costs_tableau(unsigned i, unsigned j);

    bool pivot_column_tableau(unsigned j, unsigned row_index);
    bool divide_row_by_pivot(unsigned pivot_row, unsigned pivot_col);
    
    bool precise() const { return numeric_traits<T>::precise(); }

    simplex_strategy_enum simplex_strategy() const { return
            m_settings.simplex_strategy();
    }

    bool use_tableau() const { return m_settings.use_tableau(); }
    
    template <typename K>
    static void swap(vector<K> &v, unsigned i, unsigned j) {
        auto t = v[i];
        v[i] = v[j];
        v[j] = t;
    }
        
    // called when transposing row i and ii
    void transpose_basis(unsigned i, unsigned ii) {
        swap(m_basis, i, ii);
        swap(m_basis_heading, m_basis[i], m_basis[ii]);
    }

    bool column_is_in_inf_set(unsigned j) const {
        return m_inf_set.contains(j);
    }

    void update_x_with_feasibility_tracking(unsigned j, const X & v) {
        m_x[j] = v;
        track_column_feasibility(j);
    }

    void update_x_with_delta_and_track_feasibility(unsigned j, const X & del) {
        m_x[j] += del;
        track_column_feasibility(j);
    }

    void update_x_and_call_tracker(unsigned j, const X & v) {
        m_x[j] = v;
    }

    void add_delta_to_x_and_call_tracker(unsigned j, const X & delta) {
        m_x[j] += delta;
    }
    
    void track_column_feasibility(unsigned j) {
        if (column_is_feasible(j))
            remove_column_from_inf_set(j);
        else
            insert_column_into_inf_set(j);
    }
    void insert_column_into_inf_set(unsigned j) {
        m_inf_set.insert(j);
        lp_assert(!column_is_feasible(j));
    }
    void remove_column_from_inf_set(unsigned j) {
        m_inf_set.erase(j);
        lp_assert(column_is_feasible(j));
    }
    bool costs_on_nbasis_are_zeros() const {
        lp_assert(this->basis_heading_is_correct());
        for (unsigned j = 0; j < this->m_n(); j++) {
            if (this->m_basis_heading[j] < 0)
                lp_assert(is_zero(this->m_costs[j]));
        }
        return true;
    }
    unsigned & iters_with_no_cost_growing() {
        return m_iters_with_no_cost_growing;
    }

    const unsigned & iters_with_no_cost_growing() const {
        return m_iters_with_no_cost_growing;
    }

    void calculate_pivot_row(unsigned i);
    unsigned get_base_column_in_row(unsigned row_index) const {
        return m_basis[row_index];
    }
};
}
