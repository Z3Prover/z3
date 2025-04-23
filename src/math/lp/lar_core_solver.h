/*++
Copyright (c) 2017 Microsoft Corporation
Author:

    Lev Nachmanson (levnach)

--*/
#pragma once
#include "util/vector.h"
#include <string>
#include <utility>
#include <algorithm>
#include "math/lp/indexed_vector.h"
#include "math/lp/lp_primal_core_solver.h"
#include "math/lp/stacked_vector.h"
#include "util/stacked_value.h"
namespace lp {
class lar_core_solver  {
    vector<std::pair<mpq, unsigned>> m_infeasible_linear_combination;
    int m_infeasible_sum_sign; // todo: get rid of this field
    vector<numeric_pair<mpq>> m_right_sides_dummy;
    vector<mpq> m_costs_dummy;
    stacked_value<simplex_strategy_enum> m_stacked_simplex_strategy;
    vector<impq> m_r_x;  // the solution
    vector<impq> m_backup_x;

public:
    
    stacked_vector<column_type> m_column_types;
    // r - solver fields, for rational numbers

    vector<numeric_pair<mpq>> m_r_lower_bounds;
    vector<numeric_pair<mpq>> m_r_upper_bounds;
    static_matrix<mpq, numeric_pair<mpq>> m_r_A;
    stacked_vector<unsigned> m_r_pushed_basis;
    vector<unsigned>         m_r_basis;
    vector<unsigned>         m_r_nbasis;
    std_vector<int>          m_r_heading;
    

    lp_primal_core_solver<mpq, numeric_pair<mpq>> m_r_solver; // solver in rational numbers
    
    lar_core_solver(
                    lp_settings & settings,
                    const column_namer & column_names
                    );

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
        
        for (unsigned j : m_r_solver.m_pivot_row.m_index) 
            m_r_solver.print_column_bound_info(j, out);
        
        m_r_solver.print_column_bound_info(m_r_solver.m_basis[row_index], out);        
    }


    void prefix_r();
    
    // access to x:

    void backup_x() { m_backup_x = m_r_x; }

    void restore_x() {
        m_r_x = m_backup_x;
        m_r_x.reserve(m_m());
    }

    vector<impq> const& r_x() const { return m_r_x; }
    impq& r_x(unsigned j) { return m_r_x[j]; }
    impq const& r_x(unsigned j) const { return m_r_x[j]; }
    void resize_x(unsigned n) { m_r_x.resize(n); }

    unsigned m_m() const { return m_r_A.row_count();  }

    unsigned m_n() const { return m_r_A.column_count(); }
    
    bool is_tiny() const { return this->m_m() < 10 && this->m_n() < 20; }

    bool is_empty() const { return this->m_m() == 0 && this->m_n() == 0; }

    template <typename L>
    int get_sign(const L & v) { return v > zero_of_type<L>() ? 1 : (v < zero_of_type<L>() ? -1 : 0); }

    unsigned get_number_of_non_ints() const;

    void solve();

    void pivot(int entering, int leaving) { m_r_solver.pivot(entering, leaving); }
    
    bool lower_bounds_are_set() const { return true; }

    const indexed_vector<mpq> & get_pivot_row() const {
        return m_r_solver.m_pivot_row;
    }
    
    void fill_not_improvable_zero_sum();

    void push() {
        SASSERT(m_r_solver.basis_heading_is_correct());
        SASSERT(m_column_types.size() == m_r_A.column_count());
        m_stacked_simplex_strategy = settings().simplex_strategy();
        m_stacked_simplex_strategy.push();
        m_column_types.push();
        // rational     
    }

    void pop(unsigned k) {
        // rationals
        m_column_types.pop(k);
        
        m_r_x.resize(m_r_A.column_count());
        m_r_solver.m_costs.resize(m_r_A.column_count());
        m_r_solver.m_d.resize(m_r_A.column_count());
        
        m_stacked_simplex_strategy.pop(k);
        m_r_solver.m_settings.simplex_strategy() = m_stacked_simplex_strategy;
        m_infeasible_linear_combination.reset();
        SASSERT(m_r_solver.basis_heading_is_correct());
    }
    
    bool r_basis_is_OK() const {
#ifdef Z3DEBUG
        
        for (unsigned j : m_r_solver.m_basis) {
            SASSERT(m_r_solver.m_A.m_columns[j].size() == 1);
        }
        for (unsigned j =0; j < m_r_solver.m_basis_heading.size(); j++) {
            if (m_r_solver.m_basis_heading[j] >= 0) continue;
            if (m_r_solver.m_column_types[j] == column_type::fixed) continue;
            SASSERT(static_cast<unsigned>(- m_r_solver.m_basis_heading[j] - 1) < m_r_solver.m_column_types.size());
            SASSERT( m_r_solver.m_basis_heading[j] <= -1);
        }
#endif
        return true;
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
            UNREACHABLE();
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
            UNREACHABLE();
        }
        return false;
    }

    void update_delta(mpq& delta, numeric_pair<mpq> const& l, numeric_pair<mpq> const& u) const {
        SASSERT(l <= u);
        if (l.x < u.x && l.y > u.y) {
            mpq delta1 = (u.x - l.x) / (l.y - u.y);
            if (delta1 < delta) {
                delta = delta1;
            }
        }
        SASSERT(l.x + delta * l.y <= u.x + delta * u.y);
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

    bool column_is_fixed(unsigned j) const {
        return m_column_types()[j] == column_type::fixed;
    }

    bool column_is_free(unsigned j) const {
        return m_column_types()[j] == column_type::free_column;
    }

    
    const impq & lower_bound(unsigned j) const {
        SASSERT(m_column_types()[j] == column_type::fixed ||
                    m_column_types()[j] == column_type::boxed ||
                    m_column_types()[j] == column_type::lower_bound);
        return m_r_lower_bounds[j];
    }

    const impq & upper_bound(unsigned j) const {
        SASSERT(m_column_types()[j] == column_type::fixed ||
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
