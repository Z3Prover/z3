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
namespace lp {
struct polynomial {
    static mpq m_local_zero;
    // the polynomial evaluates to m_coeffs + m_a
    vector<monomial>        m_coeffs;
    mpq                     m_a; // the free coefficient
    polynomial(const vector<monomial>& p, const mpq & a) : m_coeffs(p), m_a(a) {}
    polynomial(const vector<monomial>& p) : polynomial(p, zero_of_type<mpq>()) {}
    polynomial(): m_a(zero_of_type<mpq>()) {}
    polynomial(const polynomial & p) : m_coeffs(p.m_coeffs), m_a(p.m_a) {} 
            
    const mpq & coeff(var_index j) const {
        for (const auto & t : m_coeffs) {
            if (j == t.var()) {
                return t.coeff();
            }
        }
        return m_local_zero;
    }

    polynomial &  operator+=(const polynomial & p) {
        m_a += p.m_a;
        for (const auto & t: p.m_coeffs)
            *this += monomial(t.coeff(), t.var());
        return *this;
    }

    void add(const mpq & c, const polynomial &p) {
        m_a += p.m_a * c;
            
        for (const auto & t: p.m_coeffs)
            *this += monomial(c * t.coeff(), t.var());
    }
        
    void clear() {
        m_coeffs.clear();
        m_a = zero_of_type<mpq>();
    }
        
    bool is_empty() const { return m_coeffs.size() == 0 && numeric_traits<mpq>::is_zero(m_a); }

    unsigned number_of_monomials() const { return m_coeffs.size();}

    void add(const monomial &m ){
        if (is_zero(m.coeff())) return;
        for (unsigned k = 0; k < m_coeffs.size(); k++) {
            auto & l = m_coeffs[k];
            if (m.var() == l.var()) {
                l.coeff() += m.coeff();
                if (l.coeff() == 0)
                    m_coeffs.erase(m_coeffs.begin() + k);
                return;
            }
        }
        m_coeffs.push_back(m);
        lp_assert(is_correct());
    }
        
    polynomial & operator+=(const monomial &m ){
        add(m);
        return *this;
    }

    polynomial & operator+=(const mpq &c ){
        m_a += c;
        return *this;
    }

        
    bool is_correct() const {
        std::unordered_set<var_index> s;
        for (auto & l : m_coeffs) {
            if (l.coeff() == 0)
                return false;
            s.insert(l.var());
        }
        return m_coeffs.size() == s.size();
    }

    bool var_coeff_is_unit(unsigned j) const {
        const mpq & a = coeff(j);
        return a == 1 || a == -1;
    }

    template <typename c> // c plays a role of a map from indices to impq
    mpq value(const c& v) const {
        mpq r = m_a;
        for (auto & p : m_coeffs)
            r += v[p.var()].x * p.coeff();
        return r;
    }
    
    const vector<monomial> & coeffs() const { return m_coeffs; }
};
}
