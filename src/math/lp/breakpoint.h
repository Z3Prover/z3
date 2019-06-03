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

namespace lp {
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
