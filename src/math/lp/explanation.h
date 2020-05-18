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
#include "math/lp/lp_utils.h"
#include "util/map.h"
#include "util/optional.h"
namespace lp {
class explanation {
    u_map<optional<mpq>> m_j_to_mpq;   
public:
    explanation() {}
    template <typename T>
    explanation(const T& t) { for ( unsigned c : t) add(c); }
    
    void clear() { m_j_to_mpq.reset(); }
    void push_justification(constraint_index j, const mpq& v) {
        SASSERT(m_j_to_mpq.contains(j) == false); // if we hit the assert then we
                                                                  // might start using summation
        m_j_to_mpq.insert(j, optional<mpq>(v));
    }
    
    void push_justification(constraint_index j) {
        if (m_j_to_mpq.contains(j))
            return;
        m_j_to_mpq.insert(j, optional<mpq>());
    }

    void push_back(constraint_index j) {
        push_justification(j);
    }
    
    void add(const explanation& e) {
        for (const auto& p: e.m_j_to_mpq) {
            m_j_to_mpq.insert(p.m_key, p.m_value);
        }
    }
    template <typename T>
    void add_expl(const T& e) { for (auto j: e) add(j); }
    void add(unsigned ci) { push_justification(ci); }
    
    void add(const std::pair<mpq, constraint_index>& j) { push_justification(j.second, j.first); }

    bool empty() const {  return m_j_to_mpq.empty();  }
    size_t size() const { return m_j_to_mpq.size(); }

    class cimpq {
        constraint_index m_var;
        const optional<mpq> & m_coeff;
    public:
        cimpq(constraint_index var, const optional<mpq> & val) : m_var(var), m_coeff(val) { }
        constraint_index ci() const { return m_var; }
        mpq coeff() const { return m_coeff.undef()? one_of_type<mpq>(): *m_coeff; }
    };
    class iterator {
        u_map<optional<mpq>>::iterator m_it; 
    public:
        cimpq operator*() const {
            return cimpq(m_it->m_key, m_it->m_value);
        }        
        iterator operator++() { iterator i = *this; m_it++; return i;  }
        iterator operator++(int) { m_it++; return *this; }
        iterator(u_map<optional<mpq>>::iterator it) : m_it(it) {}
        bool operator==(const iterator &other) const { return m_it == other.m_it; }
        bool operator!=(const iterator &other) const { return !(*this == other); }
    };

    iterator begin() const { return iterator(m_j_to_mpq.begin()); }
    iterator end() const { return iterator(m_j_to_mpq.end()); }

};
}
