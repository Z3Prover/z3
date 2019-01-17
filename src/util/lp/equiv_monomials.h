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
namespace nla {
struct const_iterator_equiv_mon {
    // fields
    vector<const unsigned_vector*>                      m_same_abs_vals;
    vector<unsigned_vector::const_iterator>             m_its;
    bool                                                m_done;
    std::function<unsigned (const unsigned_vector&)>    m_find_monomial;
    // constructor for begin()
    const_iterator_equiv_mon(vector<const unsigned_vector*> abs_vals,
                             std::function<unsigned (const unsigned_vector&)> find_monomial)
        : m_same_abs_vals(abs_vals),
          m_done(false),
          m_find_monomial(find_monomial) {
        for (auto it: abs_vals){
            m_its.push_back(it->begin());
        }
    }
    // constructor for end()
    const_iterator_equiv_mon() : m_done(true) {}
        
    //typedefs
    typedef const_iterator_equiv_mon self_type;
    typedef unsigned value_type;
    typedef unsigned reference;
    typedef int difference_type;
    typedef std::forward_iterator_tag iterator_category;

    void advance() {
        if (m_done)
            return;
        unsigned k = 0;
        for (; k < m_its.size(); k++) {
            auto & it = m_its[k];
            it++;
            const auto & evars = *(m_same_abs_vals[k]);
            if (it == evars.end()) {
                it = evars.begin();
            } else {
                break;
            }
        }
            
        if (k == m_its.size()) {
            m_done = true;
        }
    }

    unsigned_vector get_key() const {
        unsigned_vector r;
        for(const auto& it : m_its){
            r.push_back(*it);
        }
        std::sort(r.begin(), r.end());
        return r;
    }
        
    self_type operator++() {self_type i = *this; operator++(1); return i;}
    self_type operator++(int) { advance(); return *this; }

    bool operator==(const self_type &other) const { return m_done == other.m_done;}
    bool operator!=(const self_type &other) const { return ! (*this == other); }
    reference operator*() const {
        return m_find_monomial(get_key());
    }
};

struct equiv_monomials {
    const monomial &                                    m_mon;
    std::function<const unsigned_vector*(lpvar)>        m_abs_eq_vars;
    std::function<unsigned (const unsigned_vector&)>    m_find_monomial;
    equiv_monomials(const monomial & m,
                    std::function<const unsigned_vector*(lpvar)> abs_eq_vars,
                    std::function<unsigned (const unsigned_vector&)> find_monomial) :
        m_mon(m),
        m_abs_eq_vars(abs_eq_vars),
        m_find_monomial(find_monomial) {}

    vector<const unsigned_vector*> vars_eqs() const {
        vector<const unsigned_vector*> r;
        for(lpvar j : m_mon.vars()) {
            r.push_back(m_abs_eq_vars(j));
        }
        return r;
    } 
    const_iterator_equiv_mon begin() const {
        return const_iterator_equiv_mon(vars_eqs(), m_find_monomial);
    }
    const_iterator_equiv_mon end() const {
        return const_iterator_equiv_mon();
    }
};
} // end of namespace nla
