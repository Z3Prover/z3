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
#include "util/lp/lp_settings.h"
#include "util/lp/lar_constraints.h"
namespace lp {
struct bound_signature {
    unsigned m_i;
    bool m_at_low;
    bound_signature(unsigned i, bool at_low) :m_i(i), m_at_low(m_at_low) {}
    bool at_upper_bound() const { return !m_at_lower_bound;}
    bool at_lower_bound() const { return m_at_low;}
};
template <typename X> 
struct signature_bound_evidence {
    vector<bound_signature> m_evidence;
    unsigned m_j; // found new bound
    bool m_lower_bound;    
    X m_bound;
};
}
