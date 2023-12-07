/*++
  Copyright (c) 2017 Microsoft Corporation

  Author:
    Lev Nachmanson (levnach)
    Nikolaj Bjorner (nbjorner)

  --*/
#pragma once
#include "math/lp/monic.h"    
#include "math/lp/factorization.h"    
#include "math/lp/nla_common.h"    


namespace nla {
class core;
class new_lemma;
struct basics: common {
    basics(core *core);
    bool basic_sign_lemma_on_two_monics(const monic& m, const monic& n);

    void basic_sign_lemma_model_based_one_mon(const monic& m, int product_sign);
    
    bool basic_sign_lemma_model_based();
    bool basic_sign_lemma_on_mon(unsigned i, std::unordered_set<unsigned> & explore);

    /**
     * \brief <generate lemma by using the fact that -ab = (-a)b) and
     -ab = a(-b)
    */
    bool basic_sign_lemma(bool derived);
    bool basic_lemma_for_mon_zero(const monic& rm, const factorization& f);

    void basic_lemma_for_mon_zero_model_based(const monic& rm, const factorization& f);

    void basic_lemma_for_mon_non_zero_model_based(const monic& rm, const factorization& f);
    // x = 0 or y = 0 -> xy = 0
    void basic_lemma_for_mon_non_zero_model_based_rm(const monic& rm, const factorization& f);

    // x = 0 or y = 0 -> xy = 0
    bool basic_lemma_for_mon_non_zero_derived(const monic& rm, const factorization& f);

    // use the fact that
    // |xabc| = |x| and x != 0 -> |a| = |b| = |c| = 1 
    bool basic_lemma_for_mon_neutral_monic_to_factor_model_based(const monic& rm, const factorization& f);
    // use the fact that
    // |xabc| = |x| and x != 0 -> |a| = |b| = |c| = 1 
    // bool basic_lemma_for_mon_neutral_monic_to_factor_model_based_fm(const monic& m);
    bool basic_lemma_for_mon_neutral_monic_to_factor_derived(const monic& rm, const factorization& f);

    // use the fact
    // 1 * 1 ... * 1 * x * 1 ... * 1 = x
    template <typename T>
    bool can_create_lemma_for_mon_neutral_from_factors_to_monic_model_based(const monic& rm, const T&, lpvar&, rational&);
    // use the fact
    // 1 * 1 ... * 1 * x * 1 ... * 1 = x
    bool basic_lemma_for_mon_neutral_from_factors_to_monic_model_based(const monic& rm, const factorization& f);
    // use the fact
    // 1 * 1 ... * 1 * x * 1 ... * 1 = x
    bool basic_lemma_for_mon_neutral_from_factors_to_monic_model_based_fm(const monic& m);
    // use the fact
    // 1 * 1 ... * 1 * x * 1 ... * 1 = x
    bool basic_lemma_for_mon_neutral_from_factors_to_monic_derived(const monic& rm, const factorization& f);
    void basic_lemma_for_mon_neutral_model_based(const monic& rm, const factorization& f);
    
    bool basic_lemma_for_mon_neutral_derived(const monic& rm, const factorization& factorization);

    void basic_lemma_for_mon_model_based(const monic& rm);

    bool basic_lemma_for_mon_derived(const monic& rm);
    
    // Use basic multiplication properties to create a lemma
    // for the given monic.
    // "derived" means derived from constraints - the alternative is model based
    void basic_lemma_for_mon(const monic& rm, bool derived);
    // use basic multiplication properties to create a lemma
    bool basic_lemma(bool derived);
    void generate_sign_lemma(const monic& m, const monic& n, const rational& sign);
    void generate_zero_lemmas(const monic& m);
    lpvar find_best_zero(const monic& m, unsigned_vector & fixed_zeros) const;
    bool try_get_non_strict_sign_from_bounds(lpvar j, int& sign) const;
    void get_non_strict_sign(lpvar j, int& sign) const;
    void add_trivial_zero_lemma(lpvar zero_j, const monic& m);
    void generate_strict_case_zero_lemma(const monic& m, unsigned zero_j, int sign_of_zj);
    
    void add_fixed_zero_lemma(const monic& m, lpvar j);
    void negate_strict_sign(new_lemma& lemma, lpvar j);
    // x != 0 or y = 0 => |xy| >= |y|
    void proportion_lemma_model_based(const monic& rm, const factorization& factorization);
    // if there are no zero factors then |m| >= |m[factor_index]|
    void generate_pl_on_mon(const monic& m, unsigned factor_index);
    
    // none of the factors is zero and the product is not zero
    // -> |fc[factor_index]| <= |rm|
    void generate_pl(const monic& rm, const factorization& fc, int factor_index);   
    bool is_separated_from_zero(const factorization&) const;
};
}
