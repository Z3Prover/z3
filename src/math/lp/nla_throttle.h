/*++
  Copyright (c) 2017 Microsoft Corporation

  Author:
    Lev Nachmanson (levnach)

  --*/
#pragma once
#include "math/lp/nla_defs.h"
#include "math/lp/lp_settings.h"
#include "util/hashtable.h"
#include "util/trail.h"
#include <cstring>

namespace nla {

class nla_throttle {
public:
    enum throttle_kind {
        ORDER_LEMMA,            // order lemma (9 params)
        BINOMIAL_SIGN_LEMMA,    // binomial sign (6 params) 
        MONOTONE_LEMMA,         // monotonicity (2 params)
        TANGENT_LEMMA           // tangent lemma (5 params: monic_var, x_var, y_var, below, plane_type)
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
    lp::statistics& m_stats;
    
    
public:
    nla_throttle(trail_stack& trail, lp::statistics& stats) : m_trail(trail), m_stats(stats) {}
    
    // Monotone lemma: mvar + is_lt
    bool insert_new(throttle_kind k, lpvar mvar, bool is_lt);
    
    // Binomial sign: xy_var + x + y + sign + sy
    bool insert_new(throttle_kind k, lpvar xy_var, lpvar x, lpvar y, int sign, int sy);
    
    // Order lemma: ac_var + a + c_sign + c + bd_var + b_var + d_sign + d + ab_cmp
    bool insert_new(throttle_kind k, lpvar ac_var, lpvar a, const rational& c_sign, lpvar c,
                    lpvar bd_var, lpvar b_var, const rational& d_sign, lpvar d, llc ab_cmp);
    
    // Tangent lemma: monic_var + x_var + y_var + below + plane_type
    bool insert_new(throttle_kind k, lpvar monic_var, lpvar x_var, lpvar y_var, bool below, int plane_type);
    
    // Tangent lemma (simplified): monic_var + x_var + y_var + below
    bool insert_new(throttle_kind k, lpvar monic_var, lpvar x_var, lpvar y_var, bool below);

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
