/*++
Copyright (c) 2016 Microsoft Corporation

Module Name:

    max_cliques.h

Abstract:

    Utility for enumerating locally maximal sub cliques.

Author:

    Nikolaj Bjorner (nbjorner) 2016-11-18

Notes:


--*/

#include "util/vector.h"
#include "util/uint_set.h"


template<class T>
class max_cliques : public T {
    using T::negate;

    vector<unsigned_vector> m_next, m_tc;
    uint_set                m_reachable[2];
    uint_set                m_seen1, m_seen2;
    unsigned_vector         m_todo;

    void get_reachable(unsigned p, uint_set const& goal, uint_set& reachable) {
        m_seen1.reset();
        m_todo.reset();
        m_todo.push_back(p);
        for (unsigned i = 0; i < m_todo.size(); ++i) {
            p = m_todo[i];
            if (m_seen1.contains(p)) {
                continue;
            }
            m_seen1.insert(p);
            if (m_seen2.contains(p)) {
                unsigned_vector const& tc = m_tc[p];
                for (unsigned j = 0; j < tc.size(); ++j) {
                    unsigned np = tc[j];
                    if (goal.contains(np)) {
                        reachable.insert(np);
                    }
                }
            }
            else {
                unsigned np = negate(p);
                if (goal.contains(np)) {
                    reachable.insert(np);
                }
                m_todo.append(next(np));
            }
        }
        for (unsigned i = m_todo.size(); i > 0; ) {
            --i;
            p = m_todo[i];
            if (m_seen2.contains(p)) {
                continue;
            }
            m_seen2.insert(p);
            unsigned np = negate(p);
            unsigned_vector& tc = m_tc[p];
            if (goal.contains(np)) {
                tc.push_back(np);
            }
            else {
                unsigned_vector const& succ = next(np);
                for (unsigned j = 0; j < succ.size(); ++j) {
                    tc.append(m_tc[succ[j]]);
                }
            }
        }
    }

    



    unsigned_vector const& next(unsigned vertex) const { return m_next[vertex]; }
    
public:
    void add_edge(unsigned src, unsigned dst) {
        m_next.reserve(std::max(src, dst) + 1);
        m_next.reserve(std::max(negate(src), negate(dst)) + 1);
        m_next[src].push_back(dst);
        m_next[dst].push_back(src);
    }

    void cliques(unsigned_vector const& ps, vector<unsigned_vector>& cliques) {     
        unsigned max = 0;
        unsigned num_ps = ps.size();
        for (unsigned i = 0; i < num_ps; ++i) {
            unsigned  p = ps[i];
            unsigned np = negate(p);
            max = std::max(max, std::max(np, p) + 1);
        }
        m_next.reserve(max);
        m_tc.reserve(m_next.size());
        unsigned_vector clique;
        uint_set vars;
        for (unsigned i = 0; i < num_ps; ++i) {
            vars.insert(ps[i]);
        }

        while (!vars.empty()) {
            clique.reset();
            bool turn = false;
            m_reachable[turn] = vars;
            while (!m_reachable[turn].empty()) {
                unsigned p = *m_reachable[turn].begin();
                m_reachable[turn].remove(p);
                vars.remove(p);
                clique.push_back(p);
                if (m_reachable[turn].empty()) {
                    break;
                }
                m_reachable[!turn].reset();
                get_reachable(p, m_reachable[turn], m_reachable[!turn]);
                turn = !turn;
            }
            if (clique.size() > 1) {
                if (clique.size() == 2 && clique[0] == negate(clique[1])) {
                    // no op
                }
                else {
                    cliques.push_back(clique);
                }
            }
        }
    }


};
