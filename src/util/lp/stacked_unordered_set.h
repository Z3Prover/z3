/*
  Copyright (c) 2017 Microsoft Corporation
  Author: Lev Nachmanson
*/

#pragma once
// this class implements an unordered_set with some stack functionality
#include <unordered_set>
#include <set>
#include <stack>
namespace lean {

template <typename A, 
          typename Hash = std::hash<A>,
          typename KeyEqual = std::equal_to<A>,
          typename Allocator = std::allocator<A>
          > class stacked_unordered_set {
    struct delta {
        std::unordered_set<A, Hash, KeyEqual> m_inserted;
        std::unordered_set<A, Hash, KeyEqual> m_erased;
        std::unordered_set<A, Hash, KeyEqual> m_deb_copy;
    };
    std::unordered_set<A, Hash, KeyEqual, Allocator> m_set;
    std::stack<delta> m_stack;
public:
    void insert(const A & a) {
        if (m_stack.empty()) {
            m_set.insert(a);
        } else if (m_set.find(a) == m_set.end()) {
            m_set.insert(a);
            size_t in_erased = m_stack.top().m_erased.erase(a);
            if (in_erased == 0) {
                m_stack.top().m_inserted.insert(a);
            }
        }
    }

    void erase(const A &a) {
        if (m_stack.empty()) {
            m_set.erase(a);
            return;
        }
        auto erased = m_set.erase(a);
        if (erased == 1) {
            auto was_new = m_stack.top().m_inserted.erase(a);
            if (was_new == 0) {
                m_stack.top().m_erased.insert(a);
            }
        }
    }
    
    unsigned size() const {
        return m_set.size();
    }

    bool contains(A & key) const {
        return m_set.find(key) != m_set.end();
    }

    bool contains(A && key) const {
        return m_set.find(std::move(key)) != m_set.end();
    }
    
    void push() {
        delta d;
        d.m_deb_copy = m_set;
        m_stack.push(d);
    }
    
    void pop() {
        pop(1);
    }
    void pop(unsigned k) {
        while (k-- > 0) {
            if (m_stack.empty())
                return;
            delta & d = m_stack.top();
            for (auto & t : d.m_inserted) {
                m_set.erase(t);
            }
            for (auto & t : d.m_erased) {
                m_set.insert(t);
            }
            lean_assert(d.m_deb_copy == m_set);
            m_stack.pop();
        }
    }

    const std::unordered_set<A, Hash, KeyEqual, Allocator>& operator()() const { return m_set;}
};
}

