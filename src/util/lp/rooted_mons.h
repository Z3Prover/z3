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
#include "util/lp/lp_utils.h"
namespace nla {
struct index_with_sign {
    unsigned m_i; // the index
    rational m_sign; // the sign: -1 or 1
    index_with_sign(unsigned i, rational sign) : m_i(i), m_sign(sign) {}
    index_with_sign() {}
    bool operator==(const index_with_sign& b) {
        return m_i == b.m_i && m_sign == b.m_sign;
    }
    unsigned var() const { return m_i; }
    const rational& sign() const { return m_sign; }
};
    
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
    // such that for every i and every h in m_proper_factors[i]
    // m_vector_of_rooted_monomials[i] is a proper factor of m_vector_of_rooted_monomials[h]
    std::unordered_map<unsigned, std::unordered_set<unsigned>>       m_proper_factors;

    void clear() {
        m_rooted_monomials_map.clear();
        m_vector_of_rooted_monomials.clear();
        m_rooted_monomials_containing_var.clear();
        m_proper_factors.clear();
    }
    
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

    std::unordered_map<unsigned, std::unordered_set<unsigned>>& proper_factors() {
        return m_proper_factors;
    }

    const std::unordered_map<unsigned, std::unordered_set<unsigned>>& proper_factors() const {
        return m_proper_factors;
    }

    void reduce_set_by_checking_proper_containment(std::unordered_set<unsigned>& p,
                                                   const rooted_mon & rm ) {
        for (auto it = p.begin(); it != p.end();) {
            if (lp::is_proper_factor(rm.m_vars, vec()[*it].m_vars)) {
                it++;
                continue;
            }
            auto iit = it;
            iit ++;
            p.erase(it);
            it = iit;
        }
    }

    // here i is the index of a monomial in m_vector_of_rooted_monomials
    void find_rooted_monomials_containing_rm(unsigned i_rm) {
        const auto & rm = vec()[i_rm];
    
        std::unordered_set<unsigned> p = var_map()[rm[0]];
        // TRACE("nla_solver",
        //       tout << "i_rm = " << i_rm << ", rm = ";
        //       print_rooted_monomial(rm, tout);
        //       tout << "\n rm[0] =" << rm[0] << " var = ";
        //       print_var(rm[0], tout);
        //       tout << "\n";
        //       trace_print_rms(p, tout);
        //       );
    
    
        for (unsigned k = 1; k < rm.size(); k++) {
            intersect_set(p, var_map()[rm[k]]);
        }
        // TRACE("nla_solver", trace_print_rms(p, tout););
        reduce_set_by_checking_proper_containment(p, rm);
        // TRACE("nla_solver", trace_print_rms(p, tout););
        proper_factors()[i_rm] = p;
    }

    void fill_proper_factors() {
        for (unsigned i = 0; i < vec().size(); i++) {
            find_rooted_monomials_containing_rm(i);
        }
    }

    void register_rooted_monomial_containing_vars(unsigned i_rm) {
        for (lpvar j_var : vec()[i_rm].vars()) {
            auto it = var_map().find(j_var);
            if (it == var_map().end()) {
                std::unordered_set<unsigned> s;
                s.insert(i_rm);
                var_map()[j_var] = s;
            } else {
                it->second.insert(i_rm);
            }
        }
    }
    
    void fill_rooted_monomials_containing_var() {
        for (unsigned i = 0; i < vec().size(); i++) {
            register_rooted_monomial_containing_vars(i);
        }
      
    }

    void register_key_mono_in_rooted_monomials(monomial_coeff const& mc, unsigned i_mon) {
        index_with_sign ms(i_mon, mc.coeff());
        auto it = map().find(mc.vars());
        if (it == map().end()) {
            TRACE("nla_solver", tout << "size = " << vec().size(););
            rooted_mon_info rmi(vec().size(), ms);
            map().emplace(mc.vars(), rmi);
            vec().push_back(rooted_mon(mc.vars(), i_mon, mc.coeff()));
        } 
        else {
            it->second.push_back(ms);
            TRACE("nla_solver", tout << "add ms.m_i = " << ms.m_i;);
        }
    }
};
}
