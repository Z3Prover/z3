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
#include <list>
#include "util/vector.h"
#include <string>
#include "math/lp/lp_utils.h"
#include "math/lp/core_solver_pretty_printer.h"
#include "math/lp/numeric_pair.h"
#include "math/lp/static_matrix.h"
#include "math/lp/permutation_matrix.h"
#include "math/lp/column_namer.h"
#include "util/uint_set.h"
#include "util/heap.h"

namespace lp {
struct lpvar_lt {
  bool operator()(lpvar v1, lpvar v2) const { return v1 < v2; }
};
typedef heap<lpvar_lt> lpvar_heap;
template <typename T, typename X>
X dot_product(const vector<T> & a, const vector<X> & b) {
    SASSERT(a.size() == b.size());
    auto r = zero_of_type<X>();
    for (unsigned i = 0; i < a.size(); i++) {
        r += a[i] * b[i];
    }
    return r;
}

template <typename T, typename X> // X represents the type of the x variable and the bounds
class lp_core_solver_base {    
    unsigned m_total_iterations;
    unsigned m_iters_with_no_cost_growing;
    unsigned inc_total_iterations() { ++m_settings.stats().m_total_iterations; return m_total_iterations++; }
private:
    lp_status m_status;
public:
    bool current_x_is_feasible() const {
        TRACE("feas_bug",
              if (!m_inf_heap.empty()) {
                  tout << "column " << *m_inf_heap.begin() << " is infeasible" << std::endl;
                  print_column_info(*m_inf_heap.begin(), tout);
              } else {
                  tout << "x is feasible\n";
              }
              );
        return m_inf_heap.empty();
    }
    bool current_x_is_infeasible() const { return m_inf_heap.size() != 0; }
private:
    lpvar_heap m_inf_heap;
public:
    const lpvar_heap& inf_heap() const { return m_inf_heap; }
    lpvar_heap& inf_heap() { return m_inf_heap; }
    void inf_heap_increase_size_by_one() { m_inf_heap.reserve(m_inf_heap.size() + 1); }
    bool inf_heap_contains(unsigned j) const { return m_inf_heap.contains(j); }
    unsigned inf_heap_size() const { return m_inf_heap.size(); }    
    indexed_vector<T>     m_pivot_row; // this is the real pivot row of the simplex tableu
    static_matrix<T, X> & m_A; // the matrix A
    // vector<X> const &           m_b; // the right side
    vector<unsigned> &    m_basis;
    vector<unsigned>&     m_nbasis;
    std_vector<int>&      m_basis_heading;
    vector<X> &           m_x; // a feasible solution, the first time set in the constructor
    vector<T> &           m_costs;
    lp_settings &         m_settings;
    
    const column_namer &  m_column_names;
    vector<T>             m_d; // the vector of reduced costs
    const vector<column_type> & m_column_types;
    const vector<X> &     m_lower_bounds;
    const vector<X> &     m_upper_bounds; 
    unsigned              m_nbasis_sort_counter;
    vector<unsigned>      m_trace_of_basis_change_vector; // the even positions are entering, the odd positions are leaving
    bool                  m_tracing_basis_changes;
    // these rows are changed by adding to them a multiple of the pivot row
    indexed_uint_set*     m_touched_rows = nullptr;
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
                        //vector<X> & b, // the right side vector
                        vector<unsigned> & basis,
                        vector<unsigned> & nbasis,
                        std_vector<int> & heading,
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
    void pretty_print(std::ostream & out);

    X get_cost() const {
        return dot_product(m_costs, m_x);
    }

    void add_delta_to_entering(unsigned entering, const X & delta);

    const X & get_var_value(unsigned j) const {
        return m_x[j];
    }

    void print_statistics(char const* str, X cost, std::ostream & message_stream);

    bool print_statistics_with_cost_and_check_that_the_time_is_over(X cost, std::ostream & message_stream);

    unsigned total_iterations() const { return m_total_iterations; }

    void set_total_iterations(unsigned s) { m_total_iterations = s; }

    bool at_bound(const X &x, const X & bound) const {
        return !below_bound(x, bound) && !above_bound(x, bound);
    }

    bool need_to_pivot_to_basis_tableau() const {
        unsigned m = m_A.row_count();
        for (unsigned i = 0; i < m; i++) {
            unsigned bj = m_basis[i];
            SASSERT(m_A.m_columns[bj].size() > 0);
            if (m_A.m_columns[bj].size() > 1)
                return true;
            for (const auto & c : m_A.m_columns[bj]) {
                if (m_A.get_val(c) != one_of_type<T>())
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
                    TRACE("lar_solver", tout << "reduced costs are incorrect for column j = " << j << " should be " << d << " but we have m_d[j] = " << m_d[j] << std::endl;);
                    return false;
                }
            }
        }
        return true;
    }
    
    bool below_bound(const X & x, const X & bound) const {
        return x < bound ;
    }

    bool above_bound(const X & x, const X & bound) const {
        return x > bound ;
    }

    bool x_below_low_bound(unsigned p) const {
        return below_bound(m_x[p], m_lower_bounds[p]);
    }

    
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

    bool inf_heap_is_correct() const;
    
    bool column_is_dual_feasible(unsigned j) const;

    bool d_is_not_negative(unsigned j) const;

    bool d_is_not_positive(unsigned j) const;

    bool time_is_over();

    void rs_minus_Anx(vector<X> & rs);

    bool basis_has_no_doubles() const;

    bool non_basis_has_no_doubles() const;

    bool basis_is_correctly_represented_in_heading() const ;
    bool non_basis_is_correctly_represented_in_heading(std::list<unsigned>*) const ;

    bool basis_heading_is_correct() const;

    virtual bool lower_bounds_are_set() const { return false; }
    X lower_bound_value(unsigned j) const { return m_lower_bounds[j]; }
    X upper_bound_value(unsigned j) const { return m_upper_bounds[j]; }

    column_type get_column_type(unsigned j) const {return m_column_types[j]; }

    
    X bound_span(unsigned j) const {
        return m_upper_bounds[j] - m_lower_bounds[j];
    }
        // clang-format on       
        std::string column_name(unsigned column) const;

    bool make_column_feasible(unsigned j, numeric_pair<mpq> & delta) {
        bool ret = false;
        SASSERT(m_basis_heading[j] < 0);
        const auto & x = m_x[j];
        switch (m_column_types[j]) {
        case column_type::fixed:
            SASSERT(m_lower_bounds[j] == m_upper_bounds[j]);
            if (x != m_lower_bounds[j]) {
                delta = m_lower_bounds[j] - x;
                ret = true;
            }
            break;
        case column_type::boxed:
            if (x < m_lower_bounds[j]) {
                delta = m_lower_bounds[j] - x;
                ret = true;
            }
            else if (x > m_upper_bounds[j]) {
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
            add_delta_to_x(j, delta);

        return ret;
        
    }

    bool remove_from_basis_core(unsigned entering, unsigned leaving);
    bool pivot_column_general(unsigned j, unsigned j_basic, indexed_vector<T> & w);
    void init_basic_part_of_basis_heading() {
        unsigned m = m_basis.size();
        for (unsigned i = 0; i < m; i++) {
            unsigned column = m_basis[i];
            m_basis_heading[column] = i;
        }
    }

    void init_non_basic_part_of_basis_heading() {
        this->m_nbasis.clear();
        for (unsigned j = static_cast<unsigned>(m_basis_heading.size()); j--;){
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
        TRACE("lar_solver", tout << "entering = " << entering << ", leaving = " << leaving << "\n";);
        SASSERT(m_basis_heading[entering] < 0);
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
        TRACE("lar_solver", tout << "entering = " << entering << ", leaving = " << leaving << "\n";);
        SASSERT(m_basis_heading[entering] < 0);
		SASSERT(m_basis_heading[leaving] >= 0);
        
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

    bool non_basic_columns_are_set_correctly() const {
        for (unsigned j : this->m_nbasis)
            if (!column_is_feasible(j)) {
                TRACE("lp_core", tout << "inf col "; print_column_info(j, tout) << "\n";);
                return false;
            }
        
        return true;
    }

    std::ostream& print_column_bound_info(unsigned j, std::ostream & out) const {
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
        return out;
    }

    std::ostream& print_column_info(unsigned j, std::ostream & out, bool print_nl = false, const std::string& var_prefix = "j") const {
        if (j >= m_column_types.size()) {
            out << "[" << j << "] is not present\n";
            return out;
        }

        std::stringstream strm;
        strm << m_x[j];
        std::string j_val = strm.str();
        out << var_prefix << j << " = " << std::setw(6) << j_val;
        if (j < 10)
            out << "  ";
        else if (j < 100)
            out << " ";

        if (m_basis_heading[j] >= 0)
            out << " base    ";
        else 
            out << "         ";
        switch (m_column_types[j]) {
        case column_type::fixed:
        case column_type::boxed:
            out << "[" << m_lower_bounds[j] << ", " << m_upper_bounds[j] << "]";
            break;
        case column_type::lower_bound:
            out << "[" << m_lower_bounds[j] << ", oo" << "]";
            break;
        case column_type::upper_bound:
            out << "[-oo, " << m_upper_bounds[j] << ']';
            break;
        case column_type::free_column:
            out << "[-oo, oo]";
            break;
        default:
            UNREACHABLE();
        }
        if (print_nl)
            out << "\n";
        else
            out << "\t";
        return out;
    }

    bool column_is_fixed(unsigned j) const { return this->m_column_types[j] == column_type::fixed; }

    
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

    void transpose_rows_tableau(unsigned i, unsigned ii);
    
    void pivot_to_reduced_costs_tableau(unsigned i, unsigned j);

    bool pivot_column_tableau(unsigned j, unsigned row_index);
    bool divide_row_by_pivot(unsigned pivot_row, unsigned pivot_col);
    
    simplex_strategy_enum simplex_strategy() const { return
            m_settings.simplex_strategy();
    }

    
    template <typename R>
    void swap(R &v, unsigned i, unsigned j) noexcept {
        auto t = v[i];
        v[i] = v[j];
        v[j] = t;
    }
        
    // called when transposing row i and ii
    void transpose_basis(unsigned i, unsigned ii) {
        swap(m_basis, i, ii);
        swap(m_basis_heading, m_basis[i], m_basis[ii]);
    }

    bool column_is_in_inf_heap(unsigned j) const {
        return m_inf_heap.contains(j);
    }

    bool column_is_base(unsigned j) const {
        return m_basis_heading[j] >= 0;
    }

    void add_delta_to_x_and_track_feasibility(unsigned j, const X & del) {
        TRACE("lar_solver_feas", tout << "del = " << del << ", was x[" << j << "] = " << m_x[j] << "\n";);
        m_x[j] += del;
        TRACE("lar_solver_feas", tout << "became x[" << j << "] = " << m_x[j] << "\n";);
        track_column_feasibility(j);
    }

    void update_x(unsigned j, const X & v) {
        m_x[j] = v;
        TRACE("lar_solver_feas", tout << "not tracking feas j = " << j << ", v = " << v << (column_is_feasible(j)? " feas":" non-feas") << "\n";);
    }

    void add_delta_to_x(unsigned j, const X& delta) {
        m_x[j] += delta;
        TRACE("lar_solver_feas", tout << "not tracking feas j = " << j << " v = " << m_x[j] << " delta = " << delta << (column_is_feasible(j) ? " feas" : " non-feas") << "\n";);
    }
        
    void track_column_feasibility(unsigned j) {
        if (column_is_feasible(j))
            remove_column_from_inf_heap(j);
        else
            insert_column_into_inf_heap(j);
    }
    void insert_column_into_inf_heap(unsigned j) {        
		if (!m_inf_heap.contains(j)) {
            m_inf_heap.reserve(j+1);
	        m_inf_heap.insert(j);
            TRACE("lar_solver_inf_heap", tout << "insert into inf_heap j = " << j << "\n";);
        }
        SASSERT(!column_is_feasible(j));
    }
    void remove_column_from_inf_heap(unsigned j) {
		if (m_inf_heap.contains(j)) {
            TRACE("lar_solver_inf_heap", tout << "erase from heap j = " << j << "\n";);
        	m_inf_heap.erase(j);
        }
        SASSERT(column_is_feasible(j));
    }

    void clear_inf_heap() {
        TRACE("lar_solver_feas",);
        m_inf_heap.clear();
    }
    
    bool costs_on_nbasis_are_zeros() const {
        SASSERT(this->basis_heading_is_correct());
        for (unsigned j = 0; j < this->m_n(); j++) {
            if (this->m_basis_heading[j] < 0)
                SASSERT(is_zero(this->m_costs[j]));
        }
        return true;
    }
    unsigned & iters_with_no_cost_growing() {
        return m_iters_with_no_cost_growing;
    }

    const unsigned & iters_with_no_cost_growing() const {
        return m_iters_with_no_cost_growing;
    }

    
    unsigned get_base_column_in_row(unsigned row_index) const {
        return m_basis[row_index];
    }
};
}
