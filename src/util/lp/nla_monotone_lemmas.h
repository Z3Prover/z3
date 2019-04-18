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
struct monotone: common {    
    monotone(core *core);
    void print_monotone_array(const vector<std::pair<std::vector<rational>, unsigned>>& lex_sorted,
                                  std::ostream& out) const;
    bool monotonicity_lemma_on_lex_sorted_rm_upper(const vector<std::pair<std::vector<rational>, unsigned>>& lex_sorted, unsigned i, const signed_vars& rm);
    bool monotonicity_lemma_on_lex_sorted_rm_lower(const vector<std::pair<std::vector<rational>, unsigned>>& lex_sorted, unsigned i, const signed_vars& rm);
    bool monotonicity_lemma_on_lex_sorted_rm(const vector<std::pair<std::vector<rational>, unsigned>>& lex_sorted, unsigned i, const signed_vars& rm);
    bool monotonicity_lemma_on_lex_sorted(const vector<std::pair<std::vector<rational>, unsigned>>& lex_sorted);
    bool  monotonicity_lemma_on_rms_of_same_arity(const unsigned_vector& rms);
    void monotonicity_lemma();
    void monotonicity_lemma(monomial const& m);
    void monotonicity_lemma_gt(const monomial& m, const rational& prod_val);    
    void monotonicity_lemma_lt(const monomial& m, const rational& prod_val);    
    void generate_monl_strict(const signed_vars& a, const signed_vars& b,  unsigned strict);
    void generate_monl(const signed_vars& a, const signed_vars& b);
    std::vector<rational> get_sorted_key(const signed_vars& rm) const;
    vector<std::pair<rational, lpvar>> get_sorted_key_with_vars(const signed_vars& a) const;
    void negate_abs_a_le_abs_b(lpvar a, lpvar b, bool strict);
    void negate_abs_a_lt_abs_b(lpvar a, lpvar b);
    void assert_abs_val_a_le_abs_var_b(const signed_vars& a, const signed_vars& b, bool strict);
};
}
