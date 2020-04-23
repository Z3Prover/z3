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
#include <limits>
#include <string>
#include <algorithm>
#include "util/vector.h"
#include <ostream>
#include "math/lp/lp_settings.h"
#include "math/lp/indexed_vector.h"
namespace lp {
template <typename T, typename X> class lp_core_solver_base; // forward definition

template <typename T, typename X>
class core_solver_pretty_printer {
    std::ostream & m_out;
    typedef std::string string;
    const lp_core_solver_base<T, X> & m_core_solver;
    vector<unsigned> m_column_widths;
    vector<vector<string>> m_A;
    vector<vector<string>> m_signs;
    vector<string> m_costs;
    vector<string> m_cost_signs;
    vector<string> m_lows; // low bounds
    vector<string> m_upps; // upper bounds
    vector<string> m_lows_signs;
    vector<string> m_upps_signs;
    unsigned m_rs_width;
    vector<X> m_rs;
    unsigned m_title_width;
    std::string m_cost_title;
    std::string m_basis_heading_title;
    std::string m_x_title;
    std::string m_lower_bounds_title;
    std::string m_upp_bounds_title;
    std::string m_exact_norm_title;
    std::string m_approx_norm_title;
    bool        m_squash_blanks;

    unsigned ncols() { return m_core_solver.m_A.column_count(); }
    unsigned nrows() { return m_core_solver.m_A.row_count(); }
    unsigned m_artificial_start;
    indexed_vector<T> m_w_buff;
    indexed_vector<T> m_ed_buff;
    vector<T> m_exact_column_norms;

public:
    core_solver_pretty_printer(const lp_core_solver_base<T, X > & core_solver, std::ostream & out);

    void init_costs();

    ~core_solver_pretty_printer();
    void init_rs_width();

    T current_column_norm();

    void init_m_A_and_signs();

    void init_column_widths();

    void adjust_width_with_lower_bound(unsigned column, unsigned & w);
    void adjust_width_with_upper_bound(unsigned column, unsigned & w);

    void adjust_width_with_bounds(unsigned column, unsigned & w);

    void adjust_width_with_basis_heading(unsigned column, unsigned & w) {
        w = std::max(w, (unsigned)T_to_string(m_core_solver.m_basis_heading[column]).size());
    }

    unsigned get_column_width(unsigned column);

    unsigned regular_cell_width(unsigned row, unsigned column, const std::string & name) {
        return regular_cell_string(row, column, name).size();
    }

    std::string regular_cell_string(unsigned row, unsigned column, std::string name);


    void set_coeff(vector<string>& row, vector<string> & row_signs, unsigned col, const T & t, string name);

    void print_x();

    std::string get_lower_bound_string(unsigned j);

    std::string get_upp_bound_string(unsigned j);


    void print_lows();

    void print_upps();

    string get_exact_column_norm_string(unsigned col) {
        return T_to_string(m_exact_column_norms[col]);
    }

    void print_exact_norms();

    void print_approx_norms();

    void print();

    void print_basis_heading();

    void print_bottom_line() {
        m_out << "----------------------" << std::endl;
    }

    void print_cost();

    void print_given_row(vector<string> & row, vector<string> & signs, X rst);

    void print_row(unsigned i);
    void print_blanks_local(int n, std::ostream & out);
};
}
