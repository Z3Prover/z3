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
struct explanation {
    void clear() { m_explanation.clear(); }
    vector<std::pair<mpq, constraint_index>> m_explanation;
    void push_justification(constraint_index j, const mpq& v) {
        m_explanation.push_back(std::make_pair(v, j));
    }
    void push_justification(constraint_index j) {
        m_explanation.push_back(std::make_pair(one_of_type<mpq>(), j));
    }
};
}
