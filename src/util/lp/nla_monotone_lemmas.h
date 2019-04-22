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
namespace nla {
class core;
class monotone : common {    
public:
    monotone(core *core);
    void monotonicity_lemma();
private:
    void monotonicity_lemma(monomial const& m);
    void monotonicity_lemma_gt(const monomial& m, const rational& prod_val);    
    void monotonicity_lemma_lt(const monomial& m, const rational& prod_val);    
    std::vector<rational> get_sorted_key(const monomial& rm) const;
    vector<std::pair<rational, lpvar>> get_sorted_key_with_rvars(const monomial& a) const;
    void negate_abs_a_le_abs_b(lpvar a, lpvar b, bool strict);
    void negate_abs_a_lt_abs_b(lpvar a, lpvar b);
    void assert_abs_val_a_le_abs_var_b(const monomial& a, const monomial& b, bool strict);
};
}
