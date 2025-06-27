/*++
  Copyright (c) 2017 Microsoft Corporation

  Author:
    Lev Nachmanson (levnach)

  --*/
#include "math/lp/nla_throttle.h"
#include "util/trace.h"

namespace nla {

bool nla_throttle::insert_new(throttle_kind k, lpvar mvar, bool is_lt) {
    signature sig;
    sig.m_values[0] = static_cast<unsigned>(k);
    sig.m_values[1] = static_cast<unsigned>(mvar);
    sig.m_values[2] = static_cast<unsigned>(is_lt ? 1 : 0);
    return insert_new_impl(sig);
}

bool nla_throttle::insert_new(throttle_kind k, lpvar xy_var, lpvar x, lpvar y, int sign, int sy) {
    signature sig;
    sig.m_values[0] = static_cast<unsigned>(k);
    sig.m_values[1] = static_cast<unsigned>(xy_var);
    sig.m_values[2] = static_cast<unsigned>(x);
    sig.m_values[3] = static_cast<unsigned>(y);
    sig.m_values[4] = normalize_sign(sign);
    sig.m_values[5] = normalize_sign(sy);
    return insert_new_impl(sig);
}

bool nla_throttle::insert_new(throttle_kind k, lpvar ac_var, lpvar a, const rational& c_sign, lpvar c,
                              lpvar bd_var, lpvar b_var, const rational& d_sign, lpvar d, llc ab_cmp) {
    signature sig;
    sig.m_values[0] = static_cast<unsigned>(k);
    sig.m_values[1] = static_cast<unsigned>(ac_var);
    sig.m_values[2] = static_cast<unsigned>(a);
    sig.m_values[3] = pack_rational_sign(c_sign);
    sig.m_values[4] = static_cast<unsigned>(c);
    sig.m_values[5] = static_cast<unsigned>(bd_var);
    sig.m_values[6] = static_cast<unsigned>(b_var);
    // Pack d_sign, d, and ab_cmp into the last slot
    sig.m_values[7] = (pack_rational_sign(d_sign) << 24) | 
                     ((static_cast<unsigned>(d) & 0xFFFF) << 8) |
                     (static_cast<unsigned>(ab_cmp) & 0xFF);
    return insert_new_impl(sig);
}

bool nla_throttle::insert_new(throttle_kind k, lpvar monic_var, lpvar x_var, lpvar y_var, bool below, int plane_type) {
    signature sig;
    sig.m_values[0] = static_cast<unsigned>(k);
    sig.m_values[1] = static_cast<unsigned>(monic_var);
    sig.m_values[2] = static_cast<unsigned>(x_var);
    sig.m_values[3] = static_cast<unsigned>(y_var);
    sig.m_values[4] = static_cast<unsigned>(below ? 1 : 0);
    sig.m_values[5] = static_cast<unsigned>(plane_type);
    return insert_new_impl(sig);
}

bool nla_throttle::insert_new(throttle_kind k, lpvar monic_var, lpvar x_var, lpvar y_var, bool below) {
    signature sig;
    sig.m_values[0] = static_cast<unsigned>(k);
    sig.m_values[1] = static_cast<unsigned>(monic_var);
    sig.m_values[2] = static_cast<unsigned>(x_var);
    sig.m_values[3] = static_cast<unsigned>(y_var);
    sig.m_values[4] = static_cast<unsigned>(below ? 1 : 0);
    // No plane_type parameter, so leave m_values[5] as 0
    return insert_new_impl(sig);
}

bool nla_throttle::insert_new_impl(const signature& sig) {
    if (m_seen.contains(sig)) {
        TRACE(nla_solver, tout << "throttled lemma generation\n";);
        m_stats.m_nla_throttled_lemmas++;
        return true;  // Already seen, throttle
    }
    
    m_seen.insert(sig);
    m_trail.push(insert_map(m_seen, sig));
    return false;     // New, don't throttle
}

} // namespace nla
