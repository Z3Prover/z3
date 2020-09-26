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
#include <limits>
#include <string>
#include <algorithm>
#include "math/lp/lp_utils.h"
#include "math/lp/lp_core_solver_base.h"
#include "math/lp/core_solver_pretty_printer.h"
#include "math/lp/numeric_pair.h"
namespace lp {


template <typename T, typename X>
core_solver_pretty_printer<T, X>::core_solver_pretty_printer(const lp_core_solver_base<T, X > & core_solver, std::ostream & out):
    m_out(out),
    m_core_solver(core_solver),
    m_A(core_solver.m_A.row_count(), vector<string>(core_solver.m_A.column_count(), "")),
    m_signs(core_solver.m_A.row_count(), vector<string>(core_solver.m_A.column_count(), " ")),
    m_costs(ncols(), ""),
    m_cost_signs(ncols(), " "),
    m_rs(ncols(), zero_of_type<X>()),
    m_w_buff(core_solver.m_w),
    m_ed_buff(core_solver.m_ed) {
    m_lower_bounds_title = "low";
    m_upp_bounds_title = "upp";
    m_exact_norm_title = "exact cn";
    m_approx_norm_title = "approx cn";
    m_artificial_start = std::numeric_limits<unsigned>::max();

    m_column_widths.resize(core_solver.m_A.column_count(), 0),
    init_m_A_and_signs();
    init_costs();
    init_column_widths();
    init_rs_width();
    m_cost_title = "costs";
    m_basis_heading_title = "heading";
    m_x_title = "x*";
    m_title_width = static_cast<unsigned>(std::max(std::max(m_cost_title.size(), std::max(m_basis_heading_title.size(), m_x_title.size())), m_approx_norm_title.size()));
    m_squash_blanks = ncols() > 5;
}

template <typename T, typename X> void core_solver_pretty_printer<T, X>::init_costs() {
    if (!m_core_solver.use_tableau()) {
        vector<T> local_y(m_core_solver.m_m());
        m_core_solver.solve_yB(local_y);
        for (unsigned i = 0; i < ncols(); i++) {
            if (m_core_solver.m_basis_heading[i] < 0) {
                T t = m_core_solver.m_costs[i] - m_core_solver.m_A.dot_product_with_column(local_y, i);
                set_coeff(m_costs, m_cost_signs, i, t, m_core_solver.column_name(i));
            }
        }
    } else {
        for (unsigned i = 0; i < ncols(); i++) {
            if (m_core_solver.m_basis_heading[i] < 0) {
                set_coeff(m_costs, m_cost_signs, i, m_core_solver.m_d[i], m_core_solver.column_name(i));
            }
        }
    }
}

template <typename T, typename X> core_solver_pretty_printer<T, X>::~core_solver_pretty_printer() {
}
template <typename T, typename X> void core_solver_pretty_printer<T, X>::init_rs_width() {
    m_rs_width = static_cast<unsigned>(T_to_string(m_core_solver.get_cost()).size());
    for (unsigned i = 0; i < nrows(); i++) {
        unsigned wt = static_cast<unsigned>(T_to_string(m_rs[i]).size());
        if (wt > m_rs_width) {
            m_rs_width = wt;
        }
    }
}

template <typename T, typename X> T core_solver_pretty_printer<T, X>::current_column_norm() {
    T ret = zero_of_type<T>();
    for (auto i : m_core_solver.m_ed.m_index)
        ret += m_core_solver.m_ed[i] * m_core_solver.m_ed[i];
    return ret;
}

template <typename T, typename X> void core_solver_pretty_printer<T, X>::init_m_A_and_signs() { 
    if (numeric_traits<T>::precise() && m_core_solver.m_settings.use_tableau()) {
        for (unsigned column = 0; column < ncols(); column++) {
            vector<T> t(nrows(), zero_of_type<T>());
            for (const auto & c : m_core_solver.m_A.m_columns[column]){
                t[c.var()] = m_core_solver.m_A.get_val(c);
            }

            auto const& value = m_core_solver.get_var_value(column);
             
            if (m_core_solver.column_is_fixed(column) && is_zero(value)) 
                continue;
            string name;
            if (m_core_solver.column_is_fixed(column)) 
                name = "*" + T_to_string(value);
            else 
                name = m_core_solver.column_name(column);
            for (unsigned row = 0; row < nrows(); row ++) {
                m_A[row].resize(ncols(), "");
                m_signs[row].resize(ncols(),"");
                set_coeff(
                          m_A[row],
                          m_signs[row],
                          column,
                          t[row],
                          name);
                m_rs[row] += t[row] * m_core_solver.m_x[column];
            }
        }
    } else {
        for (unsigned column = 0; column < ncols(); column++) {
            m_core_solver.solve_Bd(column, m_ed_buff, m_w_buff); // puts the result into m_core_solver.m_ed
            string name = m_core_solver.column_name(column);
            for (unsigned row = 0; row < nrows(); row ++) {
                set_coeff(
                          m_A[row],
                          m_signs[row],
                          column,
                          m_ed_buff[row],
                          name);
                m_rs[row] += m_ed_buff[row] * m_core_solver.m_x[column];
            }
            if (!m_core_solver.use_tableau())
                m_exact_column_norms.push_back(current_column_norm() + T(1)); // a conversion missing 1 -> T
        }
    }
}

template <typename T, typename X> void core_solver_pretty_printer<T, X>::init_column_widths() {
    for (unsigned i = 0; i < ncols(); i++) {
        m_column_widths[i] = get_column_width(i);
    }
}

template <typename T, typename X> void core_solver_pretty_printer<T, X>::adjust_width_with_lower_bound(unsigned column, unsigned & w) {
    if (!m_core_solver.lower_bounds_are_set()) return;
    w = std::max(w, (unsigned)T_to_string(m_core_solver.lower_bound_value(column)).size());
}
template <typename T, typename X> void core_solver_pretty_printer<T, X>::adjust_width_with_upper_bound(unsigned column, unsigned & w) {
    w = std::max(w, (unsigned)T_to_string(m_core_solver.upper_bound_value(column)).size());
}

template <typename T, typename X> void core_solver_pretty_printer<T, X>::adjust_width_with_bounds(unsigned column, unsigned & w) {
    switch (m_core_solver.get_column_type(column)) {
    case column_type::fixed:
    case column_type::boxed:
        adjust_width_with_lower_bound(column, w);
        adjust_width_with_upper_bound(column, w);
        break;
    case column_type::lower_bound:
        adjust_width_with_lower_bound(column, w);
        break;
    case column_type::upper_bound:
        adjust_width_with_upper_bound(column, w);
        break;
    case column_type::free_column:
        break;
    default:
        lp_assert(false);
        break;
    }
}


template <typename T, typename X> unsigned core_solver_pretty_printer<T, X>:: get_column_width(unsigned column) {
    unsigned w = static_cast<unsigned>(std::max((size_t)m_costs[column].size(), T_to_string(m_core_solver.m_x[column]).size()));
    adjust_width_with_bounds(column, w);
    adjust_width_with_basis_heading(column, w);
    for (unsigned i = 0; i < nrows(); i++) {
        unsigned cellw = static_cast<unsigned>(m_A[i][column].size());
        if (cellw > w) {
            w = cellw;
        }
    }
    if (!m_core_solver.use_tableau()) {
        w = std::max(w, (unsigned)T_to_string(m_exact_column_norms[column]).size());
        if (!m_core_solver.m_column_norms.empty())
            w = std::max(w, (unsigned)T_to_string(m_core_solver.m_column_norms[column]).size());
    }
    return w;
}

template <typename T, typename X> std::string core_solver_pretty_printer<T, X>::regular_cell_string(unsigned row, unsigned /* column */, std::string name) {
    T t = fabs(m_core_solver.m_ed[row]);
    if ( t == 1) return name;
    return T_to_string(t) + name;
}


template <typename T, typename X> void core_solver_pretty_printer<T, X>::set_coeff(vector<string>& row, vector<string> & row_signs, unsigned col, const T & t, string name) {
    if (numeric_traits<T>::is_zero(t)) {
        return;
    }
    if (col > 0) {
        if (t > 0) {
            row_signs[col] = "+";
            row[col] = t != 1? T_to_string(t) + name : name;
        } else {
            row_signs[col] = "-";
            row[col] = t != -1? T_to_string(-t) + name: name;
        }
    } else { // col == 0
        if (t == -1) {
            row[col] = "-" + name;
        } else if (t == 1) {
            row[col] = name;
        } else {
            row[col] = T_to_string(t) + name;
        }
    }
}


template <typename T, typename X> void core_solver_pretty_printer<T, X>::print_blanks_local(int n, std::ostream & out) {
    if (m_squash_blanks)
        n = 1;
    while (n--) {out << ' '; }
}
template <typename T, typename X> void core_solver_pretty_printer<T, X>::print_x() {
    if (ncols() == 0) {
        return;
    }

    int blanks = m_title_width + 1 - static_cast<int>(m_x_title.size());
    m_out << m_x_title;
    print_blanks_local(blanks, m_out);

    auto bh = m_core_solver.m_x;
    for (unsigned i = 0; i < ncols(); i++) {
        string s = T_to_string(bh[i]);
        int blanks = m_column_widths[i] - static_cast<int>(s.size());
        print_blanks_local(blanks, m_out);
        m_out << s << "   "; // the column interval
    }
    m_out << std::endl;
}

template <typename T, typename X> std::string core_solver_pretty_printer<T, X>::get_lower_bound_string(unsigned j) {
    switch (m_core_solver.get_column_type(j)){
    case column_type::boxed:
    case column_type::lower_bound:
    case column_type::fixed:
        if (m_core_solver.lower_bounds_are_set())
            return T_to_string(m_core_solver.lower_bound_value(j));
        else
            return std::string("0");
        break;
    default:
        return std::string();
    }
}

template <typename T, typename X> std::string core_solver_pretty_printer<T, X>::get_upp_bound_string(unsigned j) {
    switch (m_core_solver.get_column_type(j)){
    case column_type::boxed:
    case column_type::upper_bound:
    case column_type::fixed:
        return T_to_string(m_core_solver.upper_bound_value(j));
        break;
    default:
        return std::string();
    }
}


template <typename T, typename X> void core_solver_pretty_printer<T, X>::print_lows() {
    if (ncols() == 0) {
        return;
    }
    int blanks = m_title_width + 1 - static_cast<unsigned>(m_lower_bounds_title.size());
    m_out << m_lower_bounds_title;
    print_blanks_local(blanks, m_out);

    for (unsigned i = 0; i < ncols(); i++) {
        string s = get_lower_bound_string(i);
        int blanks = m_column_widths[i] - static_cast<unsigned>(s.size());
        print_blanks_local(blanks, m_out);
        m_out << s << "   "; // the column interval
    }
    m_out << std::endl;
}

template <typename T, typename X> void core_solver_pretty_printer<T, X>::print_upps() {
    if (ncols() == 0) {
        return;
    }
    int blanks = m_title_width + 1 - static_cast<unsigned>(m_upp_bounds_title.size());
    m_out << m_upp_bounds_title;
    print_blanks_local(blanks, m_out);

    for (unsigned i = 0; i < ncols(); i++) {
        string s = get_upp_bound_string(i);
        int blanks = m_column_widths[i] - static_cast<unsigned>(s.size());
        print_blanks_local(blanks, m_out);
        m_out << s << "   "; // the column interval
    }
    m_out << std::endl;
}

template <typename T, typename X> void core_solver_pretty_printer<T, X>::print_exact_norms() {
    if (m_core_solver.use_tableau()) return;
    int blanks = m_title_width + 1 - static_cast<int>(m_exact_norm_title.size());
    m_out << m_exact_norm_title;
    print_blanks_local(blanks, m_out);
    for (unsigned i = 0; i < ncols(); i++) {
        string s = get_exact_column_norm_string(i);
        int blanks = m_column_widths[i] - static_cast<int>(s.size());
        print_blanks_local(blanks, m_out);
        m_out << s << "   ";
    }
    m_out << std::endl;
}

template <typename T, typename X> void core_solver_pretty_printer<T, X>::print_approx_norms() {
    if (m_core_solver.use_tableau()) return;
    int blanks = m_title_width + 1 - static_cast<int>(m_approx_norm_title.size());
    m_out << m_approx_norm_title;
    print_blanks_local(blanks, m_out);
    for (unsigned i = 0; i < ncols(); i++) {
        string s = T_to_string(m_core_solver.m_column_norms[i]);
        int blanks = m_column_widths[i] - static_cast<int>(s.size());
        print_blanks_local(blanks, m_out);
        m_out << s << "   ";
    }
    m_out << std::endl;
}

template <typename T, typename X> void core_solver_pretty_printer<T, X>::print() {
    for (unsigned i = 0; i < nrows(); i++) {
        print_row(i);
    }
    print_bottom_line();
    print_cost();
    print_x();
    print_basis_heading();
    print_lows();
    print_upps();
    print_exact_norms();
    if (!m_core_solver.m_column_norms.empty())
        print_approx_norms();
    m_out << std::endl;
    if (m_core_solver.inf_set().size()) {
        m_out << "inf columns: ";
        print_vector(m_core_solver.inf_set(), m_out);
        m_out << std::endl;
    }
}

template <typename T, typename X> void core_solver_pretty_printer<T, X>::print_basis_heading() {
    int blanks = m_title_width + 1 - static_cast<int>(m_basis_heading_title.size());
    m_out << m_basis_heading_title;
    print_blanks_local(blanks, m_out);

    if (ncols() == 0) {
        return;
    }
    auto bh = m_core_solver.m_basis_heading;
    for (unsigned i = 0; i < ncols(); i++) {
        string s = T_to_string(bh[i]);
        int blanks = m_column_widths[i] - static_cast<unsigned>(s.size());
        print_blanks_local(blanks, m_out);
        m_out << s << "   "; // the column interval
    }
    m_out << std::endl;
}

template <typename T, typename X> void core_solver_pretty_printer<T, X>::print_cost() {
    int blanks = m_title_width + 1 - static_cast<int>(m_cost_title.size());
    m_out << m_cost_title;
    print_blanks_local(blanks, m_out);
    print_given_row(m_costs, m_cost_signs, m_core_solver.get_cost());
}

bool string_is_trivial(const std::string & s) {
    for (char c : s) {
        if (c != '0' && c != '.')
            return false;
    }
    return true;
}

template <typename T, typename X> void core_solver_pretty_printer<T, X>::print_given_row(vector<string> & row, vector<string> & signs, X rst) {
    for (unsigned col = 0; col < row.size(); col++) {
        unsigned width = m_column_widths[col];
        string s = row[col];
        if (m_squash_blanks && string_is_trivial(s))
            continue;
        int number_of_blanks = width - static_cast<unsigned>(s.size());
        lp_assert(number_of_blanks >= 0);
        m_out << signs[col] << ' ';
        print_blanks_local(number_of_blanks, m_out);
        m_out << s << ' ';
    }
    m_out << '=';

    string rs = T_to_string(rst);
    int nb = m_rs_width - static_cast<int>(rs.size());
    lp_assert(nb >= 0);
    print_blanks_local(nb + 1, m_out);
    m_out << rs << std::endl;
}

template <typename T, typename X> void core_solver_pretty_printer<T, X>::print_row(unsigned i){
    print_blanks_local(m_title_width + 1, m_out);
    auto row = m_A[i];
    auto sign_row = m_signs[i];
    auto rs = m_rs[i];
    print_given_row(row, sign_row, rs);
}
}
