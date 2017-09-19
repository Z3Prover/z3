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
    // the term evaluates to sum of m_coeffs + m_v
    std::unordered_map<unsigned, mpq> m_coeffs;
    mpq m_v;
    lar_term() {}
    void add_to_map(unsigned j, const mpq& c) {
        auto it = m_coeffs.find(j);
        if (it == m_coeffs.end()) {
            m_coeffs.emplace(j, c);
        } else {
            it->second += c;
            if (is_zero(it->second))
                m_coeffs.erase(it);
        }
    }

    unsigned size() const { return static_cast<unsigned>(m_coeffs.size()); }
    
    const std::unordered_map<unsigned, mpq> & coeffs() const {
        return m_coeffs;
    }
    
    lar_term(const vector<std::pair<mpq, unsigned>>& coeffs,
             const mpq & v) : m_v(v) {
        for (const auto & p : coeffs) {
            add_to_map(p.second, p.first);
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
            add_to_map(it_j, - b * li.m_data[it_j]);
        }
        m_coeffs.erase(it);
    }
    
    bool contains(unsigned j) const {
        return m_coeffs.find(j) != m_coeffs.end();
    }
};
}
