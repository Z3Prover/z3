
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
#include "util/rational.h"
#include "util/lp/monomial.h"

namespace nla {

struct factorization_factory;
typedef unsigned lpvar;

enum class factor_type { VAR, RM }; // RM stands for rooted monomial 

class factor {
    unsigned     m_index;
    factor_type  m_type;
public:
    factor() {}
    explicit factor(unsigned j) : factor(j, factor_type::VAR) {}
    factor(unsigned i, factor_type t) : m_index(i), m_type(t) {}
    unsigned index() const {return m_index;}
    unsigned& index() {return m_index;}
    factor_type type() const {return m_type;}
    factor_type& type() {return m_type;}
    bool is_var() const { return m_type == factor_type::VAR; }
};

inline bool operator==(const factor& a, const factor& b) {
    return a.index() == b.index() && a.type() == b.type(); 
}

inline bool operator!=(const factor& a, const factor& b) {
    return ! (a == b); 
}


class factorization {
    vector<factor>         m_vars;
public:
    bool is_empty() const { return m_vars.empty(); }
    const vector<factor> & vars() const { return m_vars; }
    factor operator[](unsigned k) const { return m_vars[k]; }
    size_t size() const { return m_vars.size(); }
    const factor* begin() const { return m_vars.begin(); }
    const factor* end() const { return m_vars.end(); }
    void push_back(factor v) {m_vars.push_back(v);}
};

struct const_iterator_mon {
    // fields
    svector<bool>                  m_mask;
    const factorization_factory *  m_ff;
    bool                           m_full_factorization_returned;

    //typedefs
    typedef const_iterator_mon self_type;
    typedef factorization value_type;
    typedef int difference_type;
    typedef std::forward_iterator_tag iterator_category;

    void init_vars_by_the_mask(unsigned_vector & k_vars, unsigned_vector & j_vars) const;
            
    bool get_factors(factor& k, factor& j, rational& sign) const;

    factorization operator*() const;
    void advance_mask();
            
    self_type operator++();
    self_type operator++(int);

    const_iterator_mon(const svector<bool>& mask, const factorization_factory *f);
    
    bool operator==(const self_type &other) const;
    bool operator!=(const self_type &other) const;
            
    factorization create_binary_factorization(factor j, factor k) const;
    
    factorization create_full_factorization() const;
};

struct factorization_factory {
    const svector<lpvar>& m_vars;
    // returns true if found
    virtual bool find_rm_monomial_of_vars(const svector<lpvar>& vars, unsigned& i) const = 0;

    factorization_factory(const svector<lpvar>& vars) :
        m_vars(vars) {
    }

    const_iterator_mon begin() const {
        // we keep the last element always in the first factor to avoid
        // repeating a pair twice
        svector<bool> mask(m_vars.size() - 1, false);
        return const_iterator_mon(mask, this);
    }
    
    const_iterator_mon end() const {
        svector<bool> mask(m_vars.size() - 1, true);
        auto it = const_iterator_mon(mask, this);
        it.m_full_factorization_returned = true;
        return it;
    } 
   
};

}
