/*++
Copyright (c) 2017 Microsoft Corporation
Author:

    Lev Nachmanson (levnach)

--*/
#pragma once
#include "util/vector.h"
#include <string>
#include <utility>
#include "math/lp/lp_core_solver_base.h"
#include <algorithm>
#include "math/lp/indexed_vector.h"
#include "math/lp/binary_heap_priority_queue.h"
#include "math/lp/breakpoint.h"
#include "math/lp/lp_primal_core_solver.h"
#include "math/lp/stacked_vector.h"
#include "math/lp/lar_solution_signature.h"
#include "util/stacked_value.h"
namespace lp {

class lar_core_solver  {
    // m_sign_of_entering is set to 1 if the entering variable needs
    // to grow and is set to -1  otherwise
    int m_sign_of_entering_delta;
    vector<std::pair<mpq, unsigned>> m_infeasible_linear_combination;
    int m_infeasible_sum_sign; // todo: get rid of this field
    vector<numeric_pair<mpq>> m_right_sides_dummy;
    vector<mpq> m_costs_dummy;
    vector<double> m_d_right_sides_dummy;
    vector<double> m_d_costs_dummy;
public:
    stacked_value<simplex_strategy_enum> m_stacked_simplex_strategy;
    stacked_vector<column_type> m_column_types;
    // r - solver fields, for rational numbers
    vector<numeric_pair<mpq>> m_r_x; // the solution
    stacked_vector<numeric_pair<mpq>> m_r_lower_bounds;
    stacked_vector<numeric_pair<mpq>> m_r_upper_bounds;
    static_matrix<mpq, numeric_pair<mpq>> m_r_A;
    stacked_vector<unsigned> m_r_pushed_basis;
    vector<unsigned>         m_r_basis;
    vector<unsigned>         m_r_nbasis;
    vector<int>              m_r_heading;
    stacked_vector<unsigned> m_r_columns_nz;
    stacked_vector<unsigned> m_r_rows_nz;
    
    // d - solver fields, for doubles
    vector<double> m_d_x; // the solution in doubles
    vector<double> m_d_lower_bounds;
    vector<double> m_d_upper_bounds;
    static_matrix<double, double> m_d_A;
    stacked_vector<unsigned> m_d_pushed_basis;
    vector<unsigned> m_d_basis;
    vector<unsigned> m_d_nbasis;
    vector<int> m_d_heading;


    lp_primal_core_solver<mpq, numeric_pair<mpq>> m_r_solver; // solver in rational numbers

    lp_primal_core_solver<double, double> m_d_solver; // solver in doubles
    
    lar_core_solver(
                    lp_settings & settings,
                    const column_namer & column_names
                    );

    lp_settings & settings() { return m_r_solver.m_settings;}

    const lp_settings & settings() const { return m_r_solver.m_settings;}
    
    int get_infeasible_sum_sign() const { return m_infeasible_sum_sign;   }

    const vector<std::pair<mpq, unsigned>> & get_infeasibility_info(int & inf_sign) const {
        inf_sign = m_infeasible_sum_sign;
        return m_infeasible_linear_combination;
    }

    void fill_not_improvable_zero_sum_from_inf_row();
    
    column_type get_column_type(unsigned j) { return m_column_types[j];}
    
    
    void print_pivot_row(std::ostream & out, unsigned row_index) const  {
        for (unsigned j : m_r_solver.m_pivot_row.m_index) {
            if (numeric_traits<mpq>::is_pos(m_r_solver.m_pivot_row.m_data[j]))
                out << "+";
            out << m_r_solver.m_pivot_row.m_data[j] << m_r_solver.column_name(j) << " ";
        }
        
        out << " +" << m_r_solver.column_name(m_r_solver.m_basis[row_index]) << std::endl;
        
        for (unsigned j : m_r_solver.m_pivot_row.m_index) {
            m_r_solver.print_column_bound_info(j, out);
        }
        m_r_solver.print_column_bound_info(m_r_solver.m_basis[row_index], out);        
    }
    

    void advance_on_sorted_breakpoints(unsigned entering);

    void change_slope_on_breakpoint(unsigned entering, breakpoint<numeric_pair<mpq>> * b, mpq & slope_at_entering);

    bool row_is_infeasible(unsigned row);

    bool row_is_evidence(unsigned row);

    bool find_evidence_row();

    void prefix_r();

    void prefix_d();

    unsigned m_m() const { return m_r_A.row_count();  }

    unsigned m_n() const { return m_r_A.column_count(); }
    
    bool is_tiny() const { return this->m_m() < 10 && this->m_n() < 20; }

    bool is_empty() const { return this->m_m() == 0 && this->m_n() == 0; }

    template <typename L>
    int get_sign(const L & v) { return v > zero_of_type<L>() ? 1 : (v < zero_of_type<L>() ? -1 : 0); }

    void fill_evidence(unsigned row);

    unsigned get_number_of_non_ints() const;

    void solve();

    bool lower_bounds_are_set() const { return true; }

    const indexed_vector<mpq> & get_pivot_row() const {
        return m_r_solver.m_pivot_row;
    }
    
    void fill_not_improvable_zero_sum();

    void pop_basis(unsigned k) {
        
            m_d_basis = m_r_basis;
            m_d_nbasis = m_r_nbasis;
            m_d_heading = m_r_heading;
        
    }

    void push() {
        lp_assert(m_r_solver.basis_heading_is_correct());
        lp_assert(!need_to_presolve_with_double_solver() || m_d_solver.basis_heading_is_correct());
        lp_assert(m_column_types.size() == m_r_A.column_count());
        m_stacked_simplex_strategy = settings().simplex_strategy();
        m_stacked_simplex_strategy.push();
        m_column_types.push();
        // rational
        m_r_lower_bounds.push();
        m_r_upper_bounds.push();
        
        m_d_A.push();
        
    }

    template <typename K> 
    void push_vector(stacked_vector<K> & pushed_vector, const vector<K> & vector) {
        lp_assert(pushed_vector.size() <= vector.size());
        for (unsigned i = 0; i < vector.size();i++) {
            if (i == pushed_vector.size()) {
                pushed_vector.push_back(vector[i]);
            } else {
                pushed_vector[i] = vector[i];
            }
        }
        pushed_vector.push();
    }

    void pop_markowitz_counts(unsigned k) {
        m_r_columns_nz.pop(k);
        m_r_rows_nz.pop(k);
        m_r_solver.m_columns_nz.resize(m_r_columns_nz.size());
        m_r_solver.m_rows_nz.resize(m_r_rows_nz.size());
        for (unsigned i = 0; i < m_r_columns_nz.size(); i++)
            m_r_solver.m_columns_nz[i] = m_r_columns_nz[i];
        for (unsigned i = 0; i < m_r_rows_nz.size(); i++)
            m_r_solver.m_rows_nz[i] = m_r_rows_nz[i];
    }

    
    void pop(unsigned k) {
        // rationals
        m_r_lower_bounds.pop(k);
        m_r_upper_bounds.pop(k);
        m_column_types.pop(k);
        
        m_r_x.resize(m_r_A.column_count());
        m_r_solver.m_costs.resize(m_r_A.column_count());
        m_r_solver.m_d.resize(m_r_A.column_count());
        
        m_d_A.pop(k);
        // doubles
        
        m_d_x.resize(m_d_A.column_count());
        pop_basis(k);
        m_stacked_simplex_strategy.pop(k);
        settings().set_simplex_strategy(m_stacked_simplex_strategy);
        lp_assert(m_r_solver.basis_heading_is_correct());
        lp_assert(!need_to_presolve_with_double_solver() || m_d_solver.basis_heading_is_correct());
    }

    bool need_to_presolve_with_double_solver() const {
        return false;
    }

    template <typename L>
    bool is_zero_vector(const vector<L> & b) {
        for (const L & m: b)
            if (!is_zero(m)) return false;
        return true;
    }


    bool update_xj_and_get_delta(unsigned j, non_basic_column_value_position pos_type, numeric_pair<mpq> & delta) {
        auto & x = m_r_x[j];
        switch (pos_type) {
        case at_lower_bound:
            if (x == m_r_solver.m_lower_bounds[j])
                return false;
            delta = m_r_solver.m_lower_bounds[j] - x;
            m_r_solver.m_x[j] = m_r_solver.m_lower_bounds[j];
            break;
        case at_fixed:
        case at_upper_bound:
            if (x == m_r_solver.m_upper_bounds[j])
                return false;
            delta = m_r_solver.m_upper_bounds[j] - x;
            x = m_r_solver.m_upper_bounds[j];
            break;
        case free_of_bounds: {
            return false;
        }
        case not_at_bound:
            switch (m_column_types[j]) {
            case column_type::free_column:
                return false;
            case column_type::upper_bound:
                delta = m_r_solver.m_upper_bounds[j] - x;
                x = m_r_solver.m_upper_bounds[j];
                break;
            case column_type::lower_bound:
                delta = m_r_solver.m_lower_bounds[j] - x;
                x = m_r_solver.m_lower_bounds[j];
                break;
            case column_type::boxed:
                if (x > m_r_solver.m_upper_bounds[j]) {
                    delta = m_r_solver.m_upper_bounds[j] - x;
                    x += m_r_solver.m_upper_bounds[j];
                } else {
                    delta = m_r_solver.m_lower_bounds[j] - x;
                    x = m_r_solver.m_lower_bounds[j];
                }
                break;
            case column_type::fixed:
                delta = m_r_solver.m_lower_bounds[j] - x;
                x = m_r_solver.m_lower_bounds[j];
                break;

            default:
                lp_assert(false);
            }
            break;
        default:
            lp_unreachable();
        }
        m_r_solver.remove_column_from_inf_set(j);
        return true;
    }

    
    
    void prepare_solver_x_with_signature_tableau(const lar_solution_signature & signature) {
        lp_assert(m_r_solver.inf_set_is_correct());
        for (auto &t : signature) {
            unsigned j = t.first;
            if (m_r_heading[j] >= 0)
                continue;
            auto pos_type = t.second;
            numeric_pair<mpq> delta;
            if (!update_xj_and_get_delta(j, pos_type, delta))
                continue;
            for (const auto & cc : m_r_solver.m_A.m_columns[j]){
                unsigned i = cc.var();
                unsigned jb = m_r_solver.m_basis[i];
                m_r_solver.add_delta_to_x_and_track_feasibility(jb, - delta * m_r_solver.m_A.get_val(cc));
            }
            
        }
        lp_assert(m_r_solver.inf_set_is_correct());
    }

    
    
    bool adjust_x_of_column(unsigned j) {
        /*
        if (m_r_solver.m_basis_heading[j] >= 0) {
            return false;
        }

        if (m_r_solver.column_is_feasible(j)) {
            return false;
        }

        m_r_solver.snap_column_to_bound_tableau(j);
        lp_assert(m_r_solver.column_is_feasible(j));
        m_r_solver.m_inf_set.erase(j);
        */
        lp_assert(false);
        return true;
    }


    bool r_basis_is_OK() const {
#ifdef Z3DEBUG
        
        for (unsigned j : m_r_solver.m_basis) {
            lp_assert(m_r_solver.m_A.m_columns[j].size() == 1);
        }
        for (unsigned j =0; j < m_r_solver.m_basis_heading.size(); j++) {
            if (m_r_solver.m_basis_heading[j] >= 0) continue;
            if (m_r_solver.m_column_types[j] == column_type::fixed) continue;
            lp_assert(static_cast<unsigned>(- m_r_solver.m_basis_heading[j] - 1) < m_r_solver.m_column_types.size());
            lp_assert( m_r_solver.m_basis_heading[j] <= -1);
        }
#endif
        return true;
    }
    
   
    void create_double_matrix(static_matrix<double, double> & A) {
        for (unsigned i = 0; i < m_r_A.row_count(); i++) {
            auto & row = m_r_A.m_rows[i];
            for (row_cell<mpq> & c : row) {
                A.add_new_element(i, c.var(), c.coeff().get_double());
            }
        }
    }

    void fill_basis_d(
                      vector<unsigned>& basis_d,
                      vector<int>& heading_d,
                      vector<unsigned>& nbasis_d){
        basis_d = m_r_basis;
        heading_d = m_r_heading;
        nbasis_d = m_r_nbasis;
    }

    template <typename L, typename K>
    void extract_signature_from_lp_core_solver(const lp_primal_core_solver<L, K> & solver, lar_solution_signature & signature) {
        signature.clear();
        lp_assert(signature.size() == 0);
        for (unsigned j = 0; j < solver.m_basis_heading.size(); j++) {
            if (solver.m_basis_heading[j] < 0) {
                signature[j] = solver.get_non_basic_column_value_position(j);
            }
        }
    }

    void get_bounds_for_double_solver() {
        unsigned n = m_n();
        m_d_lower_bounds.resize(n);
        m_d_upper_bounds.resize(n);
        double delta = find_delta_for_strict_boxed_bounds().get_double();
        if (delta > 0.000001)
            delta = 0.000001;
        for (unsigned j = 0; j < n; j++) {
            if (lower_bound_is_set(j)) {
                const auto & lb = m_r_solver.m_lower_bounds[j];
                m_d_lower_bounds[j] = lb.x.get_double() + delta * lb.y.get_double();
            }
            if (upper_bound_is_set(j)) {
                const auto & ub = m_r_solver.m_upper_bounds[j];
                m_d_upper_bounds[j] = ub.x.get_double() + delta * ub.y.get_double();
                lp_assert(!lower_bound_is_set(j) || (m_d_upper_bounds[j] >= m_d_lower_bounds[j]));
            }
        }
    }

    
    
    bool lower_bound_is_set(unsigned j) const {
        switch (m_column_types[j]) {
        case column_type::free_column:
        case column_type::upper_bound:
            return false;
        case column_type::lower_bound:
        case column_type::boxed:
        case column_type::fixed:
            return true;
        default:
            lp_assert(false);
        }
        return false;
    }
    
    bool upper_bound_is_set(unsigned j) const {
        switch (m_column_types[j]) {
        case column_type::free_column:
        case column_type::lower_bound:
            return false;
        case column_type::upper_bound:
        case column_type::boxed:
        case column_type::fixed:
            return true;
        default:
            lp_assert(false);
        }
        return false;
    }

    void update_delta(mpq& delta, numeric_pair<mpq> const& l, numeric_pair<mpq> const& u) const {
        lp_assert(l <= u);
        if (l.x < u.x && l.y > u.y) {
            mpq delta1 = (u.x - l.x) / (l.y - u.y);
            if (delta1 < delta) {
                delta = delta1;
            }
        }
        lp_assert(l.x + delta * l.y <= u.x + delta * u.y);
    }


    mpq find_delta_for_strict_boxed_bounds() const{
        mpq delta = numeric_traits<mpq>::one();
        for (unsigned j = 0; j < m_r_A.column_count(); j++ ) {
            if (m_column_types()[j] != column_type::boxed)
                continue;
            update_delta(delta, m_r_lower_bounds[j], m_r_upper_bounds[j]);
        }
        return delta;
    }

    
    mpq find_delta_for_strict_bounds(const mpq & initial_delta) const{
        mpq delta = initial_delta;
        for (unsigned j = 0; j < m_r_A.column_count(); j++ ) {
            if (lower_bound_is_set(j))
                update_delta(delta, m_r_lower_bounds[j], m_r_x[j]);
            if (upper_bound_is_set(j))
                update_delta(delta, m_r_x[j], m_r_upper_bounds[j]);
        }
        return delta;
    }

    void init_column_row_nz_for_r_solver() {
        m_r_solver.init_column_row_non_zeroes();
    }

    bool column_is_fixed(unsigned j) const {
        return m_column_types()[j] == column_type::fixed ||
            ( m_column_types()[j] == column_type::boxed &&
              m_r_solver.m_lower_bounds[j] == m_r_solver.m_upper_bounds[j]);
    }

    bool column_is_free(unsigned j) const {
        return m_column_types()[j] == column_type::free_column;
    }

    
    const impq & lower_bound(unsigned j) const {
        lp_assert(m_column_types()[j] == column_type::fixed ||
                    m_column_types()[j] == column_type::boxed ||
                    m_column_types()[j] == column_type::lower_bound);
        return m_r_lower_bounds[j];
    }

    const impq & upper_bound(unsigned j) const {
        lp_assert(m_column_types()[j] == column_type::fixed ||
                    m_column_types()[j] == column_type::boxed ||
                    m_column_types()[j] == column_type::upper_bound);
        return m_r_upper_bounds[j];
    }

    
    bool column_is_bounded(unsigned j) const {
        switch(m_column_types()[j]) {
        case column_type::fixed:
        case column_type::boxed:
            return true;
        default:
            return false;
        }
    }

    const vector<unsigned>& r_basis() const { return m_r_basis; }
    const vector<unsigned>& r_nbasis() const { return m_r_nbasis; }
};
}
