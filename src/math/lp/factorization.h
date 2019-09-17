
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
#include "math/lp/monic.h"
#include "math/lp/nla_defs.h"

namespace nla {

struct factorization_factory;

enum class factor_type { VAR, MON };

class factor {
    lpvar        m_var;
    factor_type  m_type;
    bool        m_sign;
public:
    factor(): factor(false) {}
    factor(bool sign): m_var(UINT_MAX), m_type(factor_type::VAR), m_sign(sign) {}
    explicit factor(lpvar v, factor_type t) : m_var(v), m_type(t), m_sign(false) {}
    unsigned var() const { return m_var; }
    factor_type type() const { return m_type; }
    void set(lpvar v, factor_type t) { m_var = v; m_type = t; }
    bool is_var() const { return m_type == factor_type::VAR; }
    bool operator==(factor const& other) const {
        return m_var == other.var() && m_type == other.type();
    }
    bool operator!=(factor const& other) const {
        return m_var != other.var() || m_type != other.type();
    }
    bool sign() const { return m_sign; }
    bool& sign() { return m_sign; }
    rational rat_sign() const { return m_sign? rational(-1) : rational(1); }
};


class factorization {
    svector<factor>       m_factors;
    const monic*       m_mon;
public:
    factorization(const monic* m): m_mon(m) {
        if (m != nullptr) {
            for (lpvar j : m->vars())
                m_factors.push_back(factor(j, factor_type::VAR));
        }
    }
    bool is_mon() const {
        return m_mon != nullptr;
    }
    bool is_empty() const { return m_factors.empty(); }
    const factor& operator[](unsigned k) const { return m_factors[k]; }
    factor& operator[](unsigned k) { return m_factors[k]; }
    size_t size() const { return m_factors.size(); }
    const factor* begin() const { return m_factors.begin(); }
    const factor* end() const { return m_factors.end(); }
    void push_back(factor const& v) {
        m_factors.push_back(v);
    }
    const monic& mon() const { return *m_mon; }
    void set_mon(const monic* m) { m_mon = m; }

};

struct const_iterator_mon {
    // fields
    svector<bool>                  m_mask;
    const factorization_factory *  m_ff;
    bool                           m_full_factorization_returned;

    // typedefs
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
    
    factorization create_full_factorization(const monic*) const;
};

struct factorization_factory {
    const svector<lpvar>&  m_vars;
    const monic*       m_monic;
    // returns true if found
    virtual bool find_canonical_monic_of_vars(const svector<lpvar>& vars, unsigned& i) const = 0;
    virtual bool canonize_sign(const monic& m) const = 0;
    virtual bool canonize_sign(const factorization& m) const = 0;

    factorization_factory(const svector<lpvar>& vars, const monic* m) :
        m_vars(vars), m_monic(m) {
    }

    svector<bool> get_mask() const {
        // we keep the last element always in the first factor to avoid
        // repeating a pair twice, that is why m_mask is shorter by one then m_vars
        
        return
            m_vars.size() != 2 ?
            svector<bool>(m_vars.size() - 1, false)
            :
            svector<bool>(1, true); // init mask as in the end() since the full iteration will do the job
    }
    
    const_iterator_mon begin() const {
        return const_iterator_mon(get_mask(), this);
    }
    
    const_iterator_mon end() const {
        svector<bool> mask(m_vars.size() - 1, true);
        auto it = const_iterator_mon(mask, this);
        it.m_full_factorization_returned = true;
        return it;
    }   
};

}
