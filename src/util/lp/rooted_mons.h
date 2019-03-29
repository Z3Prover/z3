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
    unsigned index() const { return m_i; }
    const rational& sign() const { return m_sign; }
    
};
    
struct rooted_mon {
    svector<lpvar>   m_vars;
    vector<index_with_sign>  m_mons; // canonize_monomial(m_mons[j]) gives m_vector_of_rooted_monomials[m_i]

    rooted_mon(const svector<lpvar>& vars, unsigned i, const rational& sign): m_vars(vars) {
        SASSERT(lp::is_non_decreasing(vars));
        push_back(index_with_sign(i, sign));
    }
    lpvar operator[](unsigned k) const { return m_vars[k];}
    unsigned size() const { return m_vars.size(); }
    unsigned orig_index() const { return m_mons.begin()->m_i; }
    const rational& orig_sign() const { return m_mons.begin()->m_sign; }
    const index_with_sign& orig() const { return *m_mons.begin(); }
    const svector<lpvar> & vars() const {return m_vars;}
    void push_back(const index_with_sign& ind_s) {
        m_mons.push_back(ind_s);
    }
};


struct rooted_mon_table {
    std::unordered_map<svector<lpvar>,
                       unsigned, // points to rms()
                       hash_svector>                                 m_vars_key_to_rm_index;
    vector<rooted_mon>                                               m_rms;
    // for every lpvar k m_mons_containing_var[k]
    // is the set of all rooted monomials containing
    // (rather the indices of those pointing to m_rms) 
    std::unordered_map<lpvar, std::unordered_set<unsigned>>          m_mons_containing_var;

    // A map from m_rms_of_rooted_monomials to a set
    // of sets of m_rms_of_rooted_monomials,
    // such that for every i and every h in m_proper_multiples[i] we have m_rms[i] as a proper factor of m_rms[h]
    std::unordered_map<unsigned, std::unordered_set<unsigned>>       m_proper_multiples;
    // points to m_rms
    svector<unsigned>                                                m_to_refine;
    // maps the indices of the regular monomials to the rooted monomial indices
    std::unordered_map<unsigned, index_with_sign>                    m_reg_to_rm;

    void print_stats(std::ostream& out) const {
        static double ratio = 1;
        double s = 0;
        for (const auto& p : m_vars_key_to_rm_index) {
            s += m_rms[p.second].m_mons.size();
        }
        double r = s /m_vars_key_to_rm_index.size();
        if (r > ratio) {
            ratio = r;
            out << "rooted mons "  << m_vars_key_to_rm_index.size() << ", ratio = " << r << "\n";
        }
    }

    const svector<unsigned>& to_refine() { return m_to_refine; }

    bool list_is_consistent(const vector<index_with_sign>& list, const std::unordered_set<unsigned>& to_refine_reg) const {
        if (list.begin() == list.end())
            return false;
        bool t = to_refine_reg.find(list.begin()->index()) == to_refine_reg.end();
        for (const auto& i_s : list) {
            bool tt = to_refine_reg.find(i_s.index()) == to_refine_reg.end();
            if (tt != t) {
                return false;
            }
        }
        return true;
    }

    bool list_contains_to_refine_reg(const vector<index_with_sign>& list, const std::unordered_set<unsigned>& to_refine_reg) const {
        // the call should happen when no derived sign lemma is found, so the assert below should hold
        SASSERT(list_is_consistent(list, to_refine_reg));
        return !(to_refine_reg.find(list.begin()->index()) == to_refine_reg.end());
    }
    
    void init_to_refine(const std::unordered_set<unsigned>& to_refine_reg) {
        SASSERT(m_to_refine.empty());
        for (unsigned i = 0; i < rms().size(); i++) {
            if (list_contains_to_refine_reg(rms()[i].m_mons, to_refine_reg))
                m_to_refine.push_back(i);
        }
        TRACE("nla_solver", tout << "rooted m_to_refine =["; print_vector(m_to_refine, tout) << "]\n";);
    }
    
    void clear() {
        m_vars_key_to_rm_index.clear();
        m_rms.clear();
        m_mons_containing_var.clear();
        m_proper_multiples.clear();
        m_to_refine.clear();
        m_reg_to_rm.clear();
    }
    
    const vector<rooted_mon>& rms() const { return m_rms; }
    vector<rooted_mon>& rms() { return m_rms; }

    const std::unordered_map<svector<lpvar>, unsigned, hash_svector> & vars_key_to_rm_index() const {
        return m_vars_key_to_rm_index;
    }

    std::unordered_map<svector<lpvar>, unsigned, hash_svector> & vars_key_to_rm_index() {
        return m_vars_key_to_rm_index;
    }

    const std::unordered_map<lpvar, std::unordered_set<unsigned>>& var_map() const {
        return m_mons_containing_var;
    }

    std::unordered_map<lpvar, std::unordered_set<unsigned>>&  var_map() {
        return m_mons_containing_var;
    }

    std::unordered_map<unsigned, std::unordered_set<unsigned>>& proper_multiples() {
        return m_proper_multiples;
    }

    const std::unordered_map<unsigned, std::unordered_set<unsigned>>& proper_multiples() const {
        return m_proper_multiples;
    }

    // here i is the index of a rooted monomial in m_rms
    void find_rooted_monomials_containing_rm(unsigned i_rm) {
        const auto & rm = rms()[i_rm];
        SASSERT(rm.size() > 1);
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
        proper_multiples()[i_rm] = p;
    }

    void fill_proper_multiples() {
        for (unsigned i = 0; i < rms().size(); i++) {
            find_rooted_monomials_containing_rm(i);
        }
    }

    void register_rooted_monomial_containing_vars(unsigned i_rm) {
        for (lpvar j_var : rms()[i_rm].vars()) {
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
        for (unsigned i = 0; i < rms().size(); i++) {
            register_rooted_monomial_containing_vars(i);
        }
    }

    void register_key_mono_in_rooted_monomials(monomial_coeff const& mc, unsigned i_mon) {
        index_with_sign ms(i_mon, mc.coeff());
        SASSERT(abs(mc.coeff()) == rational(1));
        auto it = vars_key_to_rm_index().find(mc.vars());
        if (it == vars_key_to_rm_index().end()) {
            TRACE("nla_solver_rm", tout << "size = " << rms().size(););
            vars_key_to_rm_index().emplace(mc.vars(), rms().size());
            m_reg_to_rm.emplace(i_mon, index_with_sign(rms().size(), mc.coeff()));
            rms().push_back(rooted_mon(mc.vars(), i_mon, mc.coeff()));
        } 
        else {
            rms()[it->second].push_back(ms);
            TRACE("nla_solver_rm", tout << "add ms.m_i = " << ms.m_i;);
            m_reg_to_rm.emplace(i_mon, index_with_sign(it->second, mc.coeff()));
        }
    }

    const index_with_sign& get_rooted_mon(unsigned i_mon) const {
        return m_reg_to_rm.find(i_mon)->second;
    }
};
}
