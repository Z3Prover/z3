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
struct rooted_mon {
    svector<lpvar>   m_vars;
    index_with_sign  m_orig;
    rooted_mon(const svector<lpvar>& vars, unsigned i, const rational& sign): m_vars(vars), m_orig(i, sign) {
        SASSERT(lp::is_non_decreasing(vars));
    }
    lpvar operator[](unsigned k) const { return m_vars[k];}
    unsigned size() const { return m_vars.size(); }
    unsigned orig_index() const { return m_orig.m_i; }
    const rational& orig_sign() const { return m_orig.m_sign; }
    const svector<lpvar> & vars() const {return m_vars;}
};

struct rooted_mon_info {
    unsigned                 m_i; // index to m_vector_of_rooted_monomials
    vector<index_with_sign>  m_mons; // canonize_monomial(m_mons[j]) gives m_vector_of_rooted_monomials[m_i]
    rooted_mon_info(unsigned i, const index_with_sign& ind_s) : m_i(i) {
        m_mons.push_back(ind_s);
    }

    void push_back(const index_with_sign& ind_s) {
        m_mons.push_back(ind_s);
    }
};

struct rooted_mon_table {
    std::unordered_map<svector<lpvar>,
                       rooted_mon_info,
                       hash_svector>                                 m_rooted_monomials_map;
    vector<rooted_mon>                                               m_vector_of_rooted_monomials;
    // for every k 
    // for each i in m_rooted_monomials_containing_var[k]
    // m_vector_of_rooted_monomials[i] contains k
    std::unordered_map<lpvar, std::unordered_set<unsigned>>          m_rooted_monomials_containing_var;

    // A map from m_vector_of_rooted_monomials to a set
    // of sets of m_vector_of_rooted_monomials,
    // such that for every i and every h in m_vector_of_rooted_monomials[i]
    // m_vector_of_rooted_monomials[i] is a proper factor of m_vector_of_rooted_monomials[h]
    std::unordered_map<unsigned, std::unordered_set<unsigned>>       m_rooted_factor_to_product;

    const vector<rooted_mon>& vec() const { return m_vector_of_rooted_monomials; }
    vector<rooted_mon>& vec() { return m_vector_of_rooted_monomials; }

    const std::unordered_map<svector<lpvar>,
                             rooted_mon_info,
                             hash_svector> & map() const {
        return m_rooted_monomials_map;
    }

    std::unordered_map<svector<lpvar>,
                             rooted_mon_info,
                             hash_svector> & map() {
        return m_rooted_monomials_map;
    }

    const std::unordered_map<lpvar, std::unordered_set<unsigned>>& var_map() const {
        return m_rooted_monomials_containing_var;
    }

    std::unordered_map<lpvar, std::unordered_set<unsigned>>&  var_map() {
        return m_rooted_monomials_containing_var;
    }

};
}
