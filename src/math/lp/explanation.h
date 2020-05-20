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
    explanation(const T& t) {
        for ( unsigned c : t)
            push_back(c);
    }
    
    void clear() { m_j_to_mpq.reset(); }
    void add_with_coeff(constraint_index j, const mpq& v) {
        SASSERT(m_j_to_mpq.contains(j) == false); // if we hit the assert then we
                                                  // might start using summation
        m_j_to_mpq.insert(j, optional<mpq>(v));
    }

    // this signature is needed to use it in a template that also works for the vector type
    void push_back(constraint_index j) {
        if (m_j_to_mpq.contains(j))
            return;
        m_j_to_mpq.insert(j, optional<mpq>());
    }
    
    void add_expl(const explanation& e) {
        for (const auto& p: e.m_j_to_mpq) {
            m_j_to_mpq.insert(p.m_key, p.m_value);
        }
    }

    void add_pair(const std::pair<mpq, constraint_index>& j) {
        add_with_coeff(j.second, j.first);
    }

    bool empty() const {  return m_j_to_mpq.empty();  }
    size_t size() const { return m_j_to_mpq.size(); }

    class cimpq {
        constraint_index m_var;
        const optional<mpq> & m_coeff;
    public:
        cimpq(constraint_index var, const optional<mpq> & val) : m_var(var), m_coeff(val) { }
        constraint_index ci() const { return m_var; }
        mpq coeff() const { return m_coeff.initialized()? *m_coeff: one_of_type<mpq>(); }
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
