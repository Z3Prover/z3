/*++
  Copyright (c) 2017 Microsoft Corporation

  Author:
    Lev Nachmanson (levnach)

  --*/
#pragma once
#include "math/lp/nla_defs.h"
#include "util/hashtable.h"
#include "util/trail.h"
#include <cstring>

namespace nla {

class nla_throttle {
public:
    enum throttle_kind {
        ORDER_LEMMA,            // order lemma (9 params)
        BINOMIAL_SIGN_LEMMA,    // binomial sign (5 params) 
        MONOTONE_LEMMA          // monotonicity (2 params)
    };

private:
    struct signature {
        unsigned m_values[8];
        
        signature() { 
            std::memset(m_values, 0, sizeof(m_values)); 
        }
        
        bool operator==(const signature& other) const {
            return std::memcmp(m_values, other.m_values, sizeof(m_values)) == 0;
        }
    };
    
    struct signature_hash {
        unsigned operator()(const signature& s) const {
            unsigned hash = 0;
            for (int i = 0; i < 8; i++) {
                hash = combine_hash(hash, s.m_values[i]);
            }
            return hash;
        }
    };
    
    hashtable<signature, signature_hash, default_eq<signature>> m_seen;
    trail_stack& m_trail;
    bool m_enabled = true;
    
public:
    nla_throttle(trail_stack& trail) : m_trail(trail) {}
    
    void set_enabled(bool enabled) { m_enabled = enabled; }
    bool enabled() const { return m_enabled; }
    
    // Monotone lemma: mvar + is_lt
    bool insert_new(throttle_kind k, lpvar mvar, bool is_lt) {
        if (!m_enabled) return false;
        signature sig;
        sig.m_values[0] = static_cast<unsigned>(k);
        sig.m_values[1] = static_cast<unsigned>(mvar);
        sig.m_values[2] = static_cast<unsigned>(is_lt);
        return insert_new_impl(sig);
    }
    
    // Binomial sign: xy_var + x + y + sign + sy
    bool insert_new(throttle_kind k, lpvar xy_var, lpvar x, lpvar y, int sign, int sy) {
        if (!m_enabled) return false;
        signature sig;
        sig.m_values[0] = static_cast<unsigned>(k);
        sig.m_values[1] = static_cast<unsigned>(xy_var);
        sig.m_values[2] = static_cast<unsigned>(x);
        sig.m_values[3] = static_cast<unsigned>(y);
        sig.m_values[4] = normalize_sign(sign);
        sig.m_values[5] = normalize_sign(sy);
        return insert_new_impl(sig);
    }
    
    // Order lemma: ac_var + a + c_sign + c + bd_var + b_var + d_sign + d + ab_cmp
    bool insert_new(throttle_kind k, lpvar ac_var, lpvar a, const rational& c_sign, lpvar c,
                    lpvar bd_var, lpvar b_var, const rational& d_sign, lpvar d, llc ab_cmp) {
        if (!m_enabled) return false;
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

private:
    bool insert_new_impl(const signature& sig);
    
    // Helper functions for packing values
    static unsigned pack_rational_sign(const rational& r) {
        return r.is_pos() ? 1 : (r.is_neg() ? 255 : 0);
    }
    
    static unsigned normalize_sign(int sign) {
        return static_cast<unsigned>(sign + 127);
    }
};

}
