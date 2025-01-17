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
// represents a linear expressieon
class lar_term {
    typedef unsigned lpvar;
protected:
    u_map<mpq> m_coeffs;
    // the column index related to the term
    lpvar m_j = -1; 
public:


    // the column index related to the term
    lpvar j() const { return m_j; }
    void set_j(unsigned j) { 
        m_j = j;
    }
    void add_monomial(const mpq& c, unsigned j) {
        if (c.is_zero())
            return;
        auto *e = m_coeffs.find_core(j);        
        if (e == nullptr) {
            m_coeffs.insert(j, c);
        } else {
            e->get_data().m_value += c;
            if (e->get_data().m_value.is_zero())
                m_coeffs.erase(j);
        }
    }

    void sub_monomial(const mpq& c, unsigned j) {
        if (c.is_zero())
            return;
        auto *e = m_coeffs.find_core(j);        
        if (e == nullptr) {
            m_coeffs.insert(j, -c);
        } else {
            e->get_data().m_value -= c;
            if (e->get_data().m_value.is_zero())
                m_coeffs.erase(j);
        }
    }

    void add_var(lpvar j) {
        rational c(1);
        add_monomial(c, j);
    }

    bool is_empty() const {
        return m_coeffs.empty(); // && is_zero(m_v);
    }
    
    unsigned size() const { return static_cast<unsigned>(m_coeffs.size()); }

    u_map<mpq> const &coeffs() const {
        return m_coeffs;
    }
    
    u_map<mpq>  &coeffs() {
        return m_coeffs;
    }
    

    void subst_by_term(const lar_term& t, unsigned term_column) {
        const auto* it = this->m_coeffs.find_core(term_column);
        if (it == nullptr) return;
        mpq a = it->get_data().m_value;
        this->m_coeffs.erase(term_column);
        for (auto p : t) {
            this->add_monomial(a * p.coeff(), p.j());
        }
    }
    // constructors
    lar_term() = default;
    lar_term(lar_term&& other) noexcept = default;
    // copy assignment operator
    lar_term& operator=(const lar_term& other) = default;
    // move assignment operator
    lar_term& operator=(lar_term&& other) noexcept = default;
    ~lar_term() = default;
    lar_term(const lar_term& a) {
        for (auto const& p : a) {
            add_monomial(p.coeff(), p.var());
        }
        m_j = a.j();
    }
    
    lar_term(const vector<std::pair<mpq, unsigned>>& coeffs) {
        for (auto const& p : coeffs) {
            add_monomial(p.first, p.second);
        }
    }
    lar_term(lpvar v1, lpvar v2) {
        add_monomial(rational::one(), v1);
        add_monomial(rational::one(), v2);
    }
    lar_term(lpvar v1) {
        add_monomial(rational::one(), v1);
    }
    lar_term(rational const& a, lpvar v1) {
        add_monomial(a, v1);
    }
    lar_term(lpvar v1, rational const& b, lpvar v2) {
        add_monomial(rational::one(), v1);
        add_monomial(b, v2);
    }
    lar_term(rational const& a, lpvar v1, rational const& b, lpvar v2) {
        add_monomial(a, v1);
        add_monomial(b, v2);
    }
    bool operator==(const lar_term & a) const {  return false; } // take care not to create identical terms
    bool operator!=(const lar_term & a) const {  return ! (*this == a);}
    // some terms get used in add constraint
    // it is the same as the offset in the m_constraints

    vector<std::pair<mpq, lpvar>> coeffs_as_vector() const {
        vector<std::pair<mpq, lpvar>> ret;
        for (const auto & [c, v] :  m_coeffs) 
            ret.push_back({v, c});
        return ret;
    }

    // j is the basic variable to substitute
    void subst_in_row(unsigned j, indexed_vector<mpq> & li) {
        const auto* it = m_coeffs.find_core(j);
        if (it == nullptr) return;
        const mpq & b = it->get_data().m_value;
        for (unsigned it_j :li.m_index) {
            add_monomial(- b * li.m_data[it_j], it_j);
        }
        m_coeffs.erase(j);
    }

    
    const mpq & get_coeff(unsigned j) const {
        const auto* it = m_coeffs.find_core(j);
        SASSERT(it != nullptr);
        return it->get_data().m_value;        
    }

    mpq & get_coeff(unsigned j){
        auto* it = m_coeffs.find_core(j);
        SASSERT(it != nullptr);
        return it->get_data().m_value;        
    }

    void erase_var(unsigned j) {
        m_coeffs.erase(j);
    }
    // the monomial ax[j] is substituted by ax[k]
    void subst_index(unsigned j, unsigned k) {
        auto* it = m_coeffs.find_core(j);
        if (it == nullptr) return;
        mpq b = it->get_data().m_value;
        m_coeffs.erase(j);
        m_coeffs.insert(k, b);
    }
    
    bool contains(unsigned j) const {
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


    lar_term clone() const {
        lar_term ret;
        for (const auto& p : *this) {
            ret.add_monomial(p.coeff(), p.j());
        }
        return ret;
    }
    
    
    lar_term operator+(const lar_term& other) const {
        lar_term ret = other.clone();
        for (const auto& p : *this) {
            ret.add_monomial(p.coeff(), p.j());
        }
        return ret;
    }


    friend lar_term operator*(const mpq& k, const lar_term& term) {
        lar_term r;
        for (const auto& p : term) {
            r.add_monomial(p.coeff()*k, p.j());
        }
        return r;
    }

    friend lar_term operator-(const lar_term& a, const lar_term& b) {
        lar_term r(a);
        for (const auto& p : b) {
            r.sub_monomial(p.coeff(), p.j());
        }
        return r;
    }


    lar_term& operator+=(const lar_term& a) {
        for (const auto& p : a) {
            add_monomial(p.coeff(), p.j());
        }
        return *this;
    }

    lar_term& operator-=(const lar_term& a) {
        for (const auto& p : a) {
            sub_monomial(p.coeff(), p.j());
        }
        return *this;
    }

    
    lar_term& operator*=(mpq const& k) {
        for (auto & t : m_coeffs)
            t.m_value *= k;
        return *this;
    }
   
    void clear() {
        m_coeffs.reset();
    }

    struct ival {
        lpvar m_var;
        const mpq & m_coeff;
        ival(lpvar var, const mpq & val) : m_var(var), m_coeff(val) { }
        lpvar j() const { return m_var; }
        lpvar var() const { return m_var; }
        const mpq & coeff() const { return m_coeff; }
    };
    
    class const_iterator {
        u_map<mpq>::iterator m_it;
    public:
        ival operator*() const { return ival(m_it->m_key, m_it->m_value); }        
        const_iterator operator++() { const_iterator i = *this; m_it++; return i;  }
        const_iterator operator++(int) { m_it++; return *this; }
        const_iterator(u_map<mpq>::iterator it) : m_it(it) {}
        bool operator==(const const_iterator &other) const { return m_it == other.m_it; }
        bool operator!=(const const_iterator &other) const { return !(*this == other); }
        
    };
   
    bool is_normalized() const {
        lpvar min_var = -1;
        mpq c;
        for (ival p : *this) {
            if (p.j() < min_var) {
                min_var = p.j();
            }
        }
        lar_term r;
        for (ival p : *this) {
            if (p.j() == min_var) {
                return p.coeff().is_one();
            }
        }
        UNREACHABLE();
        return false;        
    }

    // a is the coefficient by which we divided the term to normalize it
    lar_term get_normalized_by_min_var(mpq& a) const {
        if (m_coeffs.empty()) {
            a = mpq(1, 1);
            return *this;
        }
        a = m_coeffs.begin()->m_value;
        if (a.is_one()) {
            return *this;
        }
        lar_term r;
        auto it = m_coeffs.begin();
        r.add_var(it->m_key);
        it++;
        for(;it != m_coeffs.end(); it++) {
            r.add_monomial(it->m_value / a, it->m_key);
        }
        return r;        
    }
    const_iterator begin() const { return m_coeffs.begin();}
    const_iterator end() const { return m_coeffs.end(); }
    // This iterator yields all (coefficient, variable) pairs
    // plus one final pair: (mpq(-1), j()).
    class ext_const_iterator {
        // We'll store a reference to the lar_term, and an
        // iterator into m_coeffs. Once we reach end of m_coeffs,
        // we'll yield exactly one extra pair, then we are done.
        const lar_term&           m_term;
        lar_term::const_iterator  m_it;
        bool                      m_done; // Have we gone past m_coeffs?

    public:
        // Construct either a "begin" iterator (end=false) or "end" iterator (end=true).
        ext_const_iterator(const lar_term& t, bool is_end)
            : m_term(t)
            , m_it(is_end ? t.end() : t.begin())
            , m_done(false)
        {
            // If it is_end == true, we represent a genuine end-iterator.
            if (is_end) {
                m_done = true;
            }
        }

        // Compare iterators. Two iterators are equal if both are "done" or hold the same internal iterator.
        bool operator==(ext_const_iterator const &other) const {
            // They are equal if they are both at the special extra pair or both at the same spot in m_coeffs.
            if (m_done && other.m_done) {
                return true; 
            }
            return (!m_done && !other.m_done && m_it == other.m_it);
        }

        bool operator!=(ext_const_iterator const &other) const {
            return !(*this == other);
        }

        // Return the element we point to:
        //   1) If we haven't finished m_coeffs, yield (coefficient, var).
        //   2) If we've iterated past m_coeffs exactly once, return (mpq(-1), j()).
        auto operator*() const {
            if (!m_done && m_it != m_term.end()) {
                // Normal monomial from m_coeffs
                // Each entry is of type { m_value, m_key } in this context
                return *m_it; 
            }
            else {
                // We've gone past normal entries, so return the extra pair
                // (mpq(-1), j()).
                return ival(m_term.j(), rational::minus_one());
            }
        }

        // Pre-increment
        ext_const_iterator& operator++() {
            if (!m_done && m_it != m_term.end()) {
                ++m_it;
            }
            else {
                // We were about to return that extra pair:
                // after we move once more, we are done.
                m_done = true;
            }
            return *this;
        }

        // Post-increment
        ext_const_iterator operator++(int) {
            ext_const_iterator temp(*this);
            ++(*this);
            return temp;
        }
    };

    // Return the begin/end of our extended iteration.
    //    begin: starts at first real monomial
    //    end:   marks a finalized end of iteration
    ext_const_iterator ext_coeffs_begin() const {
        return ext_const_iterator(*this, /*is_end=*/false);
    }
    ext_const_iterator ext_coeffs_end() const {
        return ext_const_iterator(*this, /*is_end=*/true);
    }

    // Provide a small helper for "range-based for":
    // for (auto & [coef, var] : myTerm.ext_coeffs()) { ... }
    struct ext_range {
        ext_const_iterator b, e;
        ext_const_iterator begin() const { return b; }
        ext_const_iterator end() const { return e; }
    };

    // return an object that can be used in range-based for loops
    ext_range ext_coeffs() const {
        return { ext_coeffs_begin(), ext_coeffs_end() };
    }

};
}
