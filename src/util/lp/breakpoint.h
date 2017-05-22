/*
  Copyright (c) 2017 Microsoft Corporation
  Author: Lev Nachmanson
*/

#pragma once

namespace lean {
enum breakpoint_type {
    low_break, upper_break, fixed_break
};
template <typename X>
struct breakpoint {
    unsigned m_j; // the basic column
    breakpoint_type m_type;
    X m_delta;
    breakpoint(){}
    breakpoint(unsigned j, X delta, breakpoint_type type):m_j(j), m_type(type), m_delta(delta) {}
};
}
