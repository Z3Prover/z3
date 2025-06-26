/*++
  Copyright (c) 2017 Microsoft Corporation

  Author:
    Lev Nachmanson (levnach)
    Nikolaj Bjorner (nbjorner)

  --*/
#pragma once
#include "math/lp/factorization.h"
#include "math/lp/nla_common.h"
#include "util/hashtable.h"
#include "util/hash.h"

namespace nla {
class core;
class lemma_builder;
class order: common {
public:
    order(core *c) : common(c) {}
    void order_lemma();
    
    // Structure to represent the key parameters for throttling generate_mon_ol
    // Optimized for memory efficiency with packed fields
    struct mon_ol_key {
        short ac_var;
        short a;
        signed char c_sign;  // -1, 0, 1 fits in signed char
        short c;
        short bd_var;
        short b_var;
        signed char d_sign;  // -1, 0, 1 fits in signed char  
        short d;
        unsigned char ab_cmp;  // llc enum fits in unsigned char
        
        // Default constructor for hashtable
        mon_ol_key() : ac_var(0), a(0), c_sign(0), c(0), bd_var(0), b_var(0), d_sign(0), d(0), ab_cmp(static_cast<unsigned char>(llc::EQ)) {}
        
        mon_ol_key(lpvar ac_var, lpvar a, const rational& c_sign_rat, lpvar c,
                   lpvar bd_var, lpvar b_var, const rational& d_sign_rat, lpvar d, llc ab_cmp)
            : ac_var(static_cast<short>(ac_var)), a(static_cast<short>(a)), 
              c_sign(c_sign_rat.is_pos() ? 1 : (c_sign_rat.is_neg() ? -1 : 0)), 
              c(static_cast<short>(c)), bd_var(static_cast<short>(bd_var)), 
              b_var(static_cast<short>(b_var)), 
              d_sign(d_sign_rat.is_pos() ? 1 : (d_sign_rat.is_neg() ? -1 : 0)), 
              d(static_cast<short>(d)), ab_cmp(static_cast<unsigned char>(ab_cmp)) {}
              
        bool operator==(const mon_ol_key& other) const {
            return ac_var == other.ac_var && a == other.a && c_sign == other.c_sign &&
                   c == other.c && bd_var == other.bd_var && b_var == other.b_var &&
                   d_sign == other.d_sign && d == other.d && ab_cmp == other.ab_cmp;
        }
    };
    
    struct mon_ol_key_hash {
        unsigned operator()(const mon_ol_key& k) const {
            // Optimized hash with better distribution using bit shifts
            unsigned h1 = (static_cast<unsigned>(k.ac_var) << 16) | static_cast<unsigned>(k.a);
            unsigned h2 = (static_cast<unsigned>(k.c_sign + 1) << 24) | 
                         (static_cast<unsigned>(k.c) << 8) | static_cast<unsigned>(k.bd_var);
            unsigned h3 = (static_cast<unsigned>(k.b_var) << 16) | 
                         ((static_cast<unsigned>(k.d_sign + 1) << 8)) | 
                         static_cast<unsigned>(k.d);
            unsigned h4 = static_cast<unsigned>(k.ab_cmp);
            
            return combine_hash(combine_hash(h1, h2), combine_hash(h3, h4));
        }
    };
    
    hashtable<mon_ol_key, mon_ol_key_hash, default_eq<mon_ol_key>> m_processed_mon_ol;
    bool throttle_mon_ol(const monic& ac, lpvar a, const rational& c_sign, lpvar c_var,
                         const monic& bd, const factor& b, const rational& d_sign, 
                         lpvar d, llc ab_cmp);
    
    // Structure to represent the key parameters for throttling order_lemma_on_binomial_sign
    // Optimized for memory efficiency with packed fields
    struct binomial_sign_key {
        short xy_var;
        short x;
        short y;
        signed char sign;
        signed char sy;
        
        // Default constructor for hashtable
        binomial_sign_key() : xy_var(0), x(0), y(0), sign(0), sy(0) {}
        
        binomial_sign_key(lpvar xy_var, lpvar x, lpvar y, int sign, int sy)
            : xy_var(static_cast<short>(xy_var)), x(static_cast<short>(x)), 
              y(static_cast<short>(y)), sign(static_cast<signed char>(sign)), 
              sy(static_cast<signed char>(sy)) {}
              
        bool operator==(const binomial_sign_key& other) const {
            return xy_var == other.xy_var && x == other.x && y == other.y &&
                   sign == other.sign && sy == other.sy;
        }
    };
    
    struct binomial_sign_key_hash {
        unsigned operator()(const binomial_sign_key& k) const {
            // Optimized hash with better distribution 
            unsigned h1 = (static_cast<unsigned>(k.xy_var) << 16) | static_cast<unsigned>(k.x);
            unsigned h2 = (static_cast<unsigned>(k.y) << 16) | 
                         ((static_cast<unsigned>(k.sign + 127) << 8)) |  // shift sign to positive range
                         static_cast<unsigned>(k.sy + 127);               // shift sy to positive range
            
            return combine_hash(h1, h2);
        }
    };
    
    hashtable<binomial_sign_key, binomial_sign_key_hash, default_eq<binomial_sign_key>> m_processed_binomial_sign;
    bool throttle_binomial_sign(const monic& xy, lpvar x, lpvar y, int sign, int sy);
    
   private:

    bool order_lemma_on_ac_and_bc_and_factors(const monic& ac,
                                              const factor& a,
                                              const factor& c,
                                              const monic& bc,
                                              const factor& b);
    
    // a >< b && c > 0  => ac >< bc
    // a >< b && c < 0  => ac <> bc
    // ac[k] plays the role of c   
    bool order_lemma_on_ac_and_bc(const monic& rm_ac,
                                  const factorization& ac_f,
                                  bool k,
                                  const monic& rm_bd);
    
    void order_lemma_on_ac_explore(const monic& rm, const factorization& ac, bool k);

    void order_lemma_on_factorization(const monic& rm, const factorization& ab);
    

    void order_lemma_on_ab_gt(lemma_builder& lemma, const monic& m, const rational& sign, lpvar a, lpvar b);
    void order_lemma_on_ab_lt(lemma_builder& lemma, const monic& m, const rational& sign, lpvar a, lpvar b);
    void order_lemma_on_ab(lemma_builder& lemma, const monic& m, const rational& sign, lpvar a, lpvar b, bool gt);
    void order_lemma_on_factor_binomial_explore(const monic& m, bool k);
    void order_lemma_on_factor_binomial_rm(const monic& ac, bool k, const monic& bd);
    void order_lemma_on_binomial_ac_bd(const monic& ac, bool k, const monic& bd, const factor& b, lpvar d);
    void order_lemma_on_binomial_sign(const monic& ac, lpvar x, lpvar y, int sign);
    void order_lemma_on_binomial(const monic& ac);
    void order_lemma_on_monic(const monic& rm);

    void generate_ol(const monic& ac,                     
                     const factor& a,
                     const factor& c,
                     const monic& bc,
                     const factor& b);

    void generate_ol_eq(const monic& ac,                     
                     const factor& a,
                     const factor& c,
                     const monic& bc,
                     const factor& b);

    void generate_mon_ol(const monic& ac,                     
                         lpvar a,
                         const rational& c_sign,
                         lpvar c,
                         const monic& bd,
                         const factor& b,
                         const rational& d_sign,
                         lpvar d,
                         llc ab_cmp);
};
}
