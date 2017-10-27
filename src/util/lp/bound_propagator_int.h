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
public:
    bound_propagator_int(cut_solver<T> & ls);
    bool has_lower_bound(unsigned) const;
    bool has_upper_bound(unsigned) const;
    bool get_lower_bound(unsigned, T &) const;
    bool get_upper_bound(unsigned, T &) const;
    void add_bound(T  v, unsigned j, bool is_low, bool coeff_before_j_is_pos, unsigned ineq_index);
};
}

