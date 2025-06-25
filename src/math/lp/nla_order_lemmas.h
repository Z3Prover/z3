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
    
    int_hashtable<int_hash, default_eq<int>> m_processed_monics;
    bool throttle_monic(const monic&, const std::string & debug_location);
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
