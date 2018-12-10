/*++
  Copyright (c) 2017 Microsoft Corporation

  Module Name:

  <name>

  Abstract:

  <abstract>

  Author:

  Lev Nachmanson (levnach)

  Revision History:


  --*/
#pragma once
#include "util/lp/indexed_vector.h"
namespace lp {
struct lar_term {
    // the term evaluates to sum of m_coeffs 
    std::unordered_map<unsigned, mpq> m_coeffs;
    // mpq m_v;
    lar_term() {}
    void add_monomial(const mpq& c, unsigned j) {
        auto it = m_coeffs.find(j);
        if (it == m_coeffs.end()) {
            m_coeffs.emplace(j, c);
        } else {
            it->second += c;
            if (is_zero(it->second))
                m_coeffs.erase(it);
        }
    }

    bool is_empty() const {
        return m_coeffs.empty(); // && is_zero(m_v);
    }
    
    unsigned size() const { return static_cast<unsigned>(m_coeffs.size()); }
    
    const std::unordered_map<unsigned, mpq> & coeffs() const {
        return m_coeffs;
    }
    
    lar_term(const vector<std::pair<mpq, unsigned>>& coeffs) {
        for (const auto & p : coeffs) {
            add_monomial(p.first, p.second);
        }
    }
    bool operator==(const lar_term & a) const {  return false; } // take care not to create identical terms
    bool operator!=(const lar_term & a) const {  return ! (*this == a);}
    // some terms get used in add constraint
    // it is the same as the offset in the m_constraints

    vector<std::pair<mpq, unsigned>> coeffs_as_vector() const {
        vector<std::pair<mpq, unsigned>> ret;
        for (const auto & p :  m_coeffs) {
            ret.push_back(std::make_pair(p.second, p.first));
        }
        return ret;
    }

    // j is the basic variable to substitute
    void subst(unsigned j, indexed_vector<mpq> & li) {
        auto it = m_coeffs.find(j);
        if (it == m_coeffs.end()) return;
        const mpq & b = it->second;
        for (unsigned it_j :li.m_index) {
            add_monomial(- b * li.m_data[it_j], it_j);
        }
        m_coeffs.erase(it);
    }
    
    bool contains(unsigned j) const {
        return m_coeffs.find(j) != m_coeffs.end();
    }

    void negate() {
        for (auto & t : m_coeffs)
            t.second.neg();
    }

    template <typename T>
    T apply(const vector<T>& x) const {
        T ret(0);
        for (const auto & t : m_coeffs) {
            ret += t.second * x[t.first];
        }
        return ret;
    }
   
    void clear() {
        m_coeffs.clear();
    }

    struct ival {
        unsigned m_var;
        const mpq & m_coeff;
        ival(unsigned var, const mpq & val) : m_var(var), m_coeff(val) {
        }
        unsigned var() const { return m_var;}
        const mpq & coeff() const { return m_coeff; }
    };
    
    struct const_iterator {
        //fields
        std::unordered_map<unsigned, mpq>::const_iterator m_it;

        typedef const_iterator self_type;
        typedef ival value_type;
        typedef ival reference;
        //        typedef std::pair<const unsigned, mpq>* pointer;
        typedef int difference_type;
        typedef std::forward_iterator_tag iterator_category;

        reference operator*() const {
            return ival(m_it->first, m_it->second);
        }
        
        self_type operator++() {  self_type i = *this; m_it++; return i;  }
        self_type operator++(int) { m_it++; return *this; }

        const_iterator(std::unordered_map<unsigned, mpq>::const_iterator it) : m_it(it) {}
        bool operator==(const self_type &other) const {
            return m_it == other.m_it;
        }
        bool operator!=(const self_type &other) const { return !(*this == other); }
    };

    const_iterator begin() const { return m_coeffs.begin();}
    const_iterator end() const { return m_coeffs.end(); }
};
}
