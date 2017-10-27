/*
  Copyright (c) 2017 Microsoft Corporation
  Author: Lev Nachmanson
*/
#pragma once
namespace lp {
struct bound_explanation_int {
    unsigned m_ineq_index;
    bool m_is_lower;
    bound_explanation_int(unsigned i, bool is_lower): m_ineq_index(i), m_is_lower(is_lower) {}
};
}
