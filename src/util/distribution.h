/*++
Copyright (c) 2023 Microsoft Corporation

Module Name:

    distribution.h

Abstract:
   
    Probabiltiy distribution 

Author:

    Nikolaj Bjorner (nbjorner) 2023-4-12

Notes:

    Distribution class works by pushing identifiers with associated scores.
    After they have been pushed, you can access a random element using choose
    or you can enumerate the elements in random order, sorted by the score probability.
    Only one iterator can be active at a time because the iterator reshuffles the registered elements.
    The requirement is not checked or enforced.

--*/
#pragma once

#include "vector.h"

class distribution {

    random_gen m_random;
    svector<std::pair<unsigned, unsigned>> m_elems;
    unsigned m_sum = 0;

    unsigned choose(unsigned sum) {
        unsigned s = m_random(sum);
        unsigned idx = 0;
        for (auto const& [j, score] : m_elems) {
            if (s < score)
                return idx;
            s -= score;
            ++idx;
        }
        UNREACHABLE();
        return 0;
    }

public:

    distribution(unsigned seed): m_random(seed) {}

    void reset() {
        m_elems.reset();
        m_sum = 0;
    }

    bool empty() const {
        return m_elems.empty();
    }

    void push(unsigned id, unsigned score) {
        SASSERT(score > 0);
        if (score > 0) {
            m_elems.push_back({id, score});
            m_sum += score;
        }
    }

    /**
       \brief choose an element at random with probability proportional to the score 
       relative to the sum of scores of other.
     */
    unsigned choose() {
        return m_elems[choose(m_sum)].first;
    }

    class iterator {
        distribution& d;
        unsigned m_sz = 0;
        unsigned m_sum = 0;
        unsigned m_index = 0;
        void next_index() {
            if (0 != m_sz)
                m_index = d.choose(m_sum);
        }
    public:
        iterator(distribution& d, bool start): d(d), m_sz(start?d.m_elems.size():0), m_sum(d.m_sum) {
            next_index();            
        }
        unsigned operator*() const { return d.m_elems[m_index].first; }
        iterator operator++() {
            m_sum -= d.m_elems[m_index].second;
            --m_sz;
            std::swap(d.m_elems[m_index], d.m_elems[m_sz]);
            next_index();
            return *this;
        }
        bool operator!=(iterator const& other) const { return m_sz != other.m_sz; }
    };

    iterator begin() { return iterator(*this, true); }
    iterator end() { return iterator(*this, false); }
};
