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
#include "math/lp/indexed_vector.h"
#include "util/map.h"
namespace lp {
class lar_term {
    typedef unsigned lpvar;
    u_map<mpq> m_coeffs;
    // std::unordered_map<unsigned, mpq> m_coeffs;

public:
    lar_term() {}

    lar_term(const vector<std::pair<mpq, lpvar>>& coeffs) {
        for (const auto & p : coeffs) {
            add_coeff_var(p.first, p.second);
        }
    }
    template <typename T>
    lar_term(const T& coeffs) {
        for (const auto & p : coeffs) {
            add_coeff_var(p.coeff(), p.var());
        }
    }
    
    void add_coeff_var(const mpq& c, lpvar j) {
        if (c.is_zero())
            return;
        
        auto it = m_coeffs.find_iterator(j);
        if (it == m_coeffs.end()) {
            m_coeffs.insert(j, c);
        } else {
            it->m_value += c;
            if (is_zero(it->m_value))
                m_coeffs.erase(j);
        }
    }
    
    void add_var(lpvar j) {
        rational c(1);
        add_coeff_var(c, j);
    }

    bool is_empty() const {
        return m_coeffs.empty();
    }
    
    unsigned size() const { return static_cast<unsigned>(m_coeffs.size()); }
    

public:
    const u_map<mpq> & coeffs() const {
        return m_coeffs;
    }
    bool operator==(const lar_term & a) const {  return m_coeffs == a.m_coeffs; }
    bool operator!=(const lar_term & a) const {  return ! (*this == a);}
    // some terms get used in add constraint
    // it is the same as the offset in the m_constraints

    vector<std::pair<mpq, lpvar>> coeffs_as_vector() const {
        vector<std::pair<mpq, lpvar>> ret;
        for (const auto & p :  m_coeffs) {
            ret.push_back(std::make_pair(p.m_value, p.m_key));
        }
        return ret;
    }

    // j is the basic variable to substitute
    void subst(lpvar j, indexed_vector<mpq> & li) {
        auto it = m_coeffs.find_iterator(j);
        if (it == m_coeffs.end()) return;
        const mpq & b = it->m_value;
        for (unsigned it_j :li.m_index) {
            add_coeff_var(- b * li.m_data[it_j], it_j);
        }
        m_coeffs.erase(j);
    }

    // substitute a*j by a*k
    // assumes that the term contans a*j
    void subst_var(lpvar j, lpvar k) {
        SASSERT(m_coeffs.find_iterator(j) != m_coeffs.end());
        mpq a = m_coeffs[j];
        m_coeffs.erase(j);
        m_coeffs.insert(k, a);
    }
    
    bool contains(lpvar j) const {
        return m_coeffs.contains(j);
    }

    void negate() {
        for (auto & t : m_coeffs)
            t.m_value.neg();
    }

    template <typename T>
    T apply(const vector<T>& x) const {
        T ret(0);
        for (const auto & t : m_coeffs) {
            ret += t.m_value * x[t.m_key];
        }
        return ret;
    }
   
    void clear() {
        m_coeffs.reset();
    }
    
    struct ival {
        lpvar m_var;
        const mpq & m_coeff;
        ival(lpvar var, const mpq & val) : m_var(var), m_coeff(val) {
        }
        lpvar var() const { return m_var;}
        const mpq & coeff() const { return m_coeff; }
    };

    struct const_iterator {
        //fields
        u_map<mpq>::iterator m_it;

        typedef const_iterator self_type;
        typedef ival value_type;
        typedef ival reference;
        //        typedef std::pair<const unsigned, mpq>* pointer;
        typedef int difference_type;
        typedef std::forward_iterator_tag iterator_category;

        reference operator*() const {
            return ival(m_it->m_key, m_it->m_value);
        }
        
        self_type operator++() {  self_type i = *this; m_it++; return i;  }
        self_type operator++(int) { m_it++; return *this; }

        const_iterator(u_map<mpq>::iterator it) : m_it(it) {}
        bool operator==(const self_type &other) const {
            return m_it == other.m_it;
        }
        bool operator!=(const self_type &other) const { return !(*this == other); }
    };

    lar_term get_normalized_by_min_var() const {
        lpvar min_var = -1;
        mpq c;
        for (const auto & p : *this) {
            if (p.var() < min_var) {
                min_var = p.var();
                c = p.coeff();
            }
        }
        lar_term r;
        for (const auto & p : *this) {
            if (p.var() != min_var) {
                r.add_coeff_var(p.coeff() / c, p.var());
            } else {
                r.add_var(min_var);
            }
        }
        return r;        
    }
    const_iterator begin() const { return const_iterator(m_coeffs.begin());}
    const_iterator end() const { return const_iterator(m_coeffs.end()); }

};
}
