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
#include <unordered_set>
#include "math/lp/lp_utils.h"
namespace lp {
class explanation {
    vector<std::pair<mpq, constraint_index>> m_explanation;
    std::unordered_set<unsigned> m_set_of_ci;
public:
    explanation() {}
    template <typename T>
    explanation(const T& t) { for ( unsigned c : t) add(c); }
    
    void clear() { m_explanation.clear(); m_set_of_ci.clear(); }
    vector<std::pair<mpq, constraint_index>>::const_iterator begin() const { return m_explanation.begin(); }
    vector<std::pair<mpq, constraint_index>>::const_iterator end() const { return m_explanation.end(); }
    void push_justification(constraint_index j, const mpq& v) {
        m_explanation.push_back(std::make_pair(v, j));
    }
    void push_justification(constraint_index j) {
        if (m_set_of_ci.find(j) != m_set_of_ci.end()) return;
        m_set_of_ci.insert(j);
        m_explanation.push_back(std::make_pair(one_of_type<mpq>(), j));
    }

    void push_back(constraint_index j) {
        push_justification(j);
    }
    
    void add(const explanation& e) { for (auto j: e.m_set_of_ci) add(j); }
    template <typename T>
    void add_expl(const T& e) { for (auto j: e) add(j); }
    void add(unsigned ci) { push_justification(ci); }
    
    void add(const std::pair<mpq, constraint_index>& j) { push_justification(j.second, j.first); }

    bool empty() const {  return m_explanation.empty();  }
    size_t size() const { return m_explanation.size(); }
};
}
