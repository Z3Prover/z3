/*
  Copyright (c) 2017 Microsoft Corporation
  Author: Lev Nachmanson
*/
#pragma once
#include "util/lp/lp_settings.h"
namespace lp {
template <typename T>
class cut_solver;
template <typename T>
class bound_propagator_int {
    cut_solver<T> & m_cut_solver;
    unsigned m_slack_var;
public:
    bound_propagator_int(cut_solver<T> & ls, unsigned);
    bool has_lower_bound(unsigned) const;
    bool has_upper_bound(unsigned) const;
    bool get_lower_bound(unsigned, T &) const;
    bool get_upper_bound(unsigned, T &) const;
    void add_bound(T  v, unsigned j, bool is_low, unsigned ineq_index);
    void print_ineq(std::ofstream & out, unsigned ineq_index) const;
    void print_var_domain(std::ofstream & out, unsigned j) const;
    std::string var_name(unsigned j) const;
};
}

