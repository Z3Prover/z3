/*
  Copyright (c) 2017 Microsoft Corporation
  Author: Lev Nachmanson
*/
#pragma once
#include "util/lp/lp_settings.h"
#include "util/lp/lar_constraints.h"
namespace lean {
struct bound_signature {
    unsigned m_i;
    bool m_at_low;
    bound_signature(unsigned i, bool at_low) :m_i(i), m_at_low(m_at_low) {}
    bool at_upper_bound() const { return !m_at_low_bound;}
    bool at_low_bound() const { return m_at_low;}
};
template <typename X> 
struct signature_bound_evidence {
    vector<bound_signature> m_evidence;
    unsigned m_j; // found new bound
    bool m_low_bound;    
    X m_bound;
};
}
