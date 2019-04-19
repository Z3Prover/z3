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
#include "util/lp/monomial.h"    
#include "util/lp/rooted_mons.h"    
#include "util/lp/factorization.h"    
#include "util/lp/nla_common.h"    


namespace nla {
class core;
struct basics: common {
    basics(core *core);
    bool basic_sign_lemma_on_two_monomials(const monomial& m, const monomial& n, const rational& sign);

    void basic_sign_lemma_model_based_one_mon(const monomial& m, int product_sign);
    
    bool basic_sign_lemma_model_based();
    bool basic_sign_lemma_on_mon(unsigned i, std::unordered_set<unsigned> & explore);

    /**
     * \brief <generate lemma by using the fact that -ab = (-a)b) and
     -ab = a(-b)
    */
    bool basic_sign_lemma(bool derived);
    bool basic_lemma_for_mon_zero(const smon& rm, const factorization& f);

    void basic_lemma_for_mon_zero_model_based(const smon& rm, const factorization& f);

    void basic_lemma_for_mon_non_zero_model_based(const smon& rm, const factorization& f);
    // x = 0 or y = 0 -> xy = 0
    void basic_lemma_for_mon_non_zero_model_based_rm(const smon& rm, const factorization& f);

    void basic_lemma_for_mon_non_zero_model_based_mf(const factorization& f);
    // x = 0 or y = 0 -> xy = 0
    bool basic_lemma_for_mon_non_zero_derived(const smon& rm, const factorization& f);

    // use the fact that
    // |xabc| = |x| and x != 0 -> |a| = |b| = |c| = 1 
    bool basic_lemma_for_mon_neutral_monomial_to_factor_model_based(const smon& rm, const factorization& f);
    // use the fact that
    // |xabc| = |x| and x != 0 -> |a| = |b| = |c| = 1 
    bool basic_lemma_for_mon_neutral_monomial_to_factor_model_based_fm(const monomial& m);
    bool basic_lemma_for_mon_neutral_monomial_to_factor_derived(const smon& rm, const factorization& f);

    // use the fact
    // 1 * 1 ... * 1 * x * 1 ... * 1 = x
    bool basic_lemma_for_mon_neutral_from_factors_to_monomial_model_based(const smon& rm, const factorization& f);
    // use the fact
    // 1 * 1 ... * 1 * x * 1 ... * 1 = x
    bool basic_lemma_for_mon_neutral_from_factors_to_monomial_model_based_fm(const monomial& m);
    // use the fact
    // 1 * 1 ... * 1 * x * 1 ... * 1 = x
    bool basic_lemma_for_mon_neutral_from_factors_to_monomial_derived(const smon& rm, const factorization& f);
    void basic_lemma_for_mon_neutral_model_based(const smon& rm, const factorization& f);
    
    bool basic_lemma_for_mon_neutral_derived(const smon& rm, const factorization& factorization);

    void basic_lemma_for_mon_model_based(const smon& rm);

    bool basic_lemma_for_mon_derived(const smon& rm);
    
    // Use basic multiplication properties to create a lemma
    // for the given monomial.
    // "derived" means derived from constraints - the alternative is model based
    void basic_lemma_for_mon(const smon& rm, bool derived);
    // use basic multiplication properties to create a lemma
    bool basic_lemma(bool derived);
    void generate_sign_lemma(const monomial& m, const monomial& n, const rational& sign);
    void generate_zero_lemmas(const monomial& m);
    lpvar find_best_zero(const monomial& m, unsigned_vector & fixed_zeros) const;
    bool try_get_non_strict_sign_from_bounds(lpvar j, int& sign) const;
    void get_non_strict_sign(lpvar j, int& sign) const;
    void add_trival_zero_lemma(lpvar zero_j, const monomial& m);
    void generate_strict_case_zero_lemma(const monomial& m, unsigned zero_j, int sign_of_zj);
    
    void add_fixed_zero_lemma(const monomial& m, lpvar j);
    void negate_strict_sign(lpvar j);
    // x != 0 or y = 0 => |xy| >= |y|
    void proportion_lemma_model_based(const smon& rm, const factorization& factorization);
    // x != 0 or y = 0 => |xy| >= |y|
    bool proportion_lemma_derived(const smon& rm, const factorization& factorization);
    // if there are no zero factors then |m| >= |m[factor_index]|
    void generate_pl_on_mon(const monomial& m, unsigned factor_index);
    
    // none of the factors is zero and the product is not zero
    // -> |fc[factor_index]| <= |rm|
    void generate_pl(const smon& rm, const factorization& fc, int factor_index);   
};
}
