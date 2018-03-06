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
class active_set {
    std::unordered_set<constraint*, constraint_hash, constraint_equal> m_cs;
public:
    std::unordered_set<constraint*, constraint_hash, constraint_equal> cs() const { return m_cs;}

    
    bool is_empty() const { return m_cs.size() == 0; }
    // 0 - low priority, 1 - high priority
    void add_constraint(constraint* c) {
        if (c->is_active()) return;
        m_cs.insert(c);
        c->set_active_flag();
    }

    void clear() {
        for (constraint * c: m_cs) {
            c->remove_active_flag();
        }
        m_cs.clear();
    }
        
        
    constraint* remove_random_constraint(unsigned rand) {
        if (m_cs.size() == 0)
            return nullptr;
        unsigned j = rand % m_cs.size();
        auto it = std::next(m_cs.begin(), j);
        constraint * c = *it;
        c->remove_active_flag();
        m_cs.erase(it);
        return c;
    }
        
    unsigned size() const {
        return static_cast<unsigned>(m_cs.size());
    }

    void remove_constraint(constraint * c) {
        m_cs.erase(c);
        c->remove_active_flag();
    }
};
}
