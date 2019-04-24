/*++
  Copyright (c) 2017 Microsoft Corporation

  Module Name:

  <name>

  Abstract:

  <abstract>

  Author:
  Nikolaj Bjorner (nbjorner)
  Lev Nachmanson (levnach)

  Revision History:


  --*/
#pragma once
#include "util/lp/rooted_mons.h"
#include "util/lp/factorization.h"
#include "util/lp/nla_common.h"

namespace nla {
class core;
class order: common {
public:
    order(core *c) : common(c) {}
    void order_lemma();
    
private:

    bool order_lemma_on_ac_and_bc_and_factors(const monomial& ac,
                                              const factor& a,
                                              const factor& c,
                                              const monomial& bc,
                                              const factor& b);
    
    // a >< b && c > 0  => ac >< bc
    // a >< b && c < 0  => ac <> bc
    // ac[k] plays the role of c   
    bool order_lemma_on_ac_and_bc(const monomial& rm_ac,
                                  const factorization& ac_f,
                                  bool k,
                                  const monomial& rm_bd);
    
    bool order_lemma_on_ac_explore(const monomial& rm, const factorization& ac, bool k);

    void order_lemma_on_factorization(const monomial& rm, const factorization& ab);
    
    /**
       \brief Add lemma: 
       a > 0 & b <= value(b) => sign*ab <= value(b)*a  if value(a) > 0
       a < 0 & b >= value(b) => sign*ab <= value(b)*a  if value(a) < 0
    */
    void order_lemma_on_ab_gt(const monomial& m, const rational& sign, lpvar a, lpvar b);
    // we need to deduce ab >= val(b)*a
    /**
       \brief Add lemma: 
       a > 0 & b >= value(b) => sign*ab >= value(b)*a if value(a) > 0
       a < 0 & b <= value(b) => sign*ab >= value(b)*a if value(a) < 0
    */
    void order_lemma_on_ab_lt(const monomial& m, const rational& sign, lpvar a, lpvar b);
    void order_lemma_on_ab(const monomial& m, const rational& sign, lpvar a, lpvar b, bool gt);
    void order_lemma_on_factor_binomial_explore(const monomial& m, bool k);
    void order_lemma_on_factor_binomial_rm(const monomial& ac, bool k, const monomial& bd);
    void order_lemma_on_binomial_ac_bd(const monomial& ac, bool k, const monomial& bd, const factor& b, lpvar d);
    void order_lemma_on_binomial_sign(const monomial& ac, lpvar x, lpvar y, int sign);
    void order_lemma_on_binomial(const monomial& ac);
    void order_lemma_on_rmonomial(const monomial& rm);
    // |c_sign| = 1, and c*c_sign > 0
    // ac > bc => ac/|c| > bc/|c| => a*c_sign > b*c_sign
    void generate_ol(const monomial& ac,                     
                     const factor& a,
                     int c_sign,
                     const factor& c,
                     const monomial& bc,
                     const factor& b,
                     llc ab_cmp);

    void generate_mon_ol(const monomial& ac,                     
                         lpvar a,
                         const rational& c_sign,
                         lpvar c,
                         const monomial& bd,
                         const factor& b,
                         const rational& d_sign,
                         lpvar d,
                         llc ab_cmp);
    void negate_var_factor_relation(const rational& a_sign, lpvar a, const rational& b_sign, const factor& b);
};
}
