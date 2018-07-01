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
#include "util/lp/binary_heap_priority_queue.h"
namespace lp {
class active_set {
    std::unordered_set<constraint*, constraint_hash, constraint_equal> m_cs;
    binary_heap_priority_queue<int>                                    m_q;
    std::unordered_map<unsigned, constraint *>                         m_id_to_constraint;
public:
    std::unordered_set<constraint*, constraint_hash, constraint_equal> cs() const { return m_cs;}

    bool contains(const constraint* c)  const {
        return m_id_to_constraint.find(c->id()) != m_id_to_constraint.end();
    }
    
    bool is_empty() const { return m_cs.size() == 0; }
    // low priority will be dequeued first
    void add_constraint(constraint* c, int priority) {
        if (contains(c))
            return;
        m_cs.insert(c);
        m_id_to_constraint[c->id()] = c;
        m_q.enqueue(c->id(), priority);
    }

    void clear() {
        m_cs.clear();
        m_id_to_constraint.clear();
        m_q.clear();
    }
        
        
    constraint* remove_constraint() {
        if (m_cs.size() == 0)
            return nullptr;
        unsigned id = m_q.dequeue();
        auto it = m_id_to_constraint.find(id);
        lp_assert(it != m_id_to_constraint.end());
        constraint* c = it->second;
        m_cs.erase(c);
        m_id_to_constraint.erase(it);
        return c;
    }
        
    unsigned size() const {
        return static_cast<unsigned>(m_cs.size());
    }

    void remove_constraint(constraint * c) {
        if (! contains(c)) return;
        
        m_cs.erase(c);
        m_id_to_constraint.erase(c->id());
        m_q.remove(c->id());
    }
};
}
