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
#pragma once

#include "util/vector.h"
#include "util/uint_set.h"
#include "util/heap.h"
#include "util/map.h"

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
            if (m_seen1.contains(p)) 
                continue;            
            m_seen1.insert(p);
            if (m_seen2.contains(p)) {
                unsigned_vector const& tc = m_tc[p];
                for (unsigned np : tc) 
                    if (goal.contains(np)) 
                        reachable.insert(np);
            }
            else {
                unsigned np = negate(p);
                if (goal.contains(np)) 
                    reachable.insert(np);                
                m_todo.append(next(np));
            }
        }
        for (unsigned i = m_todo.size(); i-- > 0; ) {            
            p = m_todo[i];
            if (m_seen2.contains(p)) 
                continue;
            m_seen2.insert(p);
            unsigned np = negate(p);
            unsigned_vector& tc = m_tc[p];
            if (goal.contains(np)) 
                tc.push_back(np);
            else 
                for (unsigned s : next(np))
                    tc.append(m_tc[s]);
        }
    }

    unsigned_vector const& next(unsigned vertex) const { return m_next[vertex]; }

    void init(unsigned_vector const& ps) {
        unsigned max = 0;
        for (unsigned p : ps) {
            unsigned np = negate(p);
            max = std::max(max, std::max(np, p) + 1);
        }
        m_next.reserve(max);
        m_tc.reserve(m_next.size());
    }

    struct compare_degree {
        u_map<uint_set>& conns;
        compare_degree(u_map<uint_set>& conns): conns(conns) {}
        bool operator()(unsigned x, unsigned y) const {
            return conns[x].num_elems() < conns[y].num_elems();
        }
    };


    void init(unsigned_vector const& ps, u_map<uint_set>& conns) {

        uint_set vars;
        
        for (unsigned p : ps) 
            vars.insert(p);
        
        for (unsigned v : ps) {
            uint_set reach;
            get_reachable(v, vars, reach);
            conns.insert(v, reach);
        }
    }
    
public:
    void add_edge(unsigned src, unsigned dst) {
        m_next.reserve(std::max(src, dst) + 1);
        m_next.reserve(std::max(negate(src), negate(dst)) + 1);
        m_next[src].push_back(dst);
        m_next[dst].push_back(src);
    }

    void cliques1(unsigned_vector const& ps, vector<unsigned_vector>& cliques) {     
        init(ps);
        unsigned_vector clique;
        uint_set vars;
        for (unsigned v : ps)
            vars.insert(v);

        while (!vars.empty()) {
            clique.reset();
            bool turn = false;
            m_reachable[turn] = vars;
            while (!m_reachable[turn].empty()) {
                unsigned p = *m_reachable[turn].begin();
                m_reachable[turn].remove(p);
                vars.remove(p);
                clique.push_back(p);
                if (m_reachable[turn].empty()) 
                    break;
                m_reachable[!turn].reset();
                get_reachable(p, m_reachable[turn], m_reachable[!turn]);
                turn = !turn;
            }
            if (clique.size() > 1) {
                if (clique.size() == 2 && clique[0] == negate(clique[1])) {
                    // no op
                }
                else 
                    cliques.push_back(clique);
            }
        }        
    }

    // better quality cliques
    void cliques2(unsigned_vector const& ps, vector<unsigned_vector>& cs) {     
        u_map<uint_set> conns;
        init(ps);
        // compute connections using TC of implication graph
        init(ps, conns);
        cliques(ps, conns, cs);
    }

    // cliques after connections are computed.
    void cliques(unsigned_vector const& ps, u_map<uint_set>& conns, vector<unsigned_vector>& cliques) {

        unsigned maxp = 1;
        for (unsigned p : ps)
            maxp = std::max(p, maxp);
        
        uint_set todo;
        compare_degree lt(conns);
        heap<compare_degree> heap(maxp + 1, lt);

        for (unsigned p : ps) {           
            todo.insert(p);
            heap.insert(p);
        }

        while (!todo.empty()) {
            unsigned v = heap.min_value();                        
            uint_set am1;
            unsigned_vector next;
            for (unsigned n : conns[v])
                if (todo.contains(n))
                    next.push_back(n);
            std::sort(next.begin(), next.end(), [&](unsigned a, unsigned b) { return conns[a].num_elems() < conns[b].num_elems(); });
            for (unsigned x : next) {
                bool all = heap.contains(x);
                for (unsigned y : am1) {
                    if (!conns[x].contains(y)) {
                        all = false;
                        break;
                    }
                }
                if (all)
                    am1.insert(x);
            }            
            am1.insert(v);

            for (unsigned x : am1) {
                todo.remove(x);
                for (unsigned y : conns[x]) {
                    conns[y].remove(x);
                    if (heap.contains(y))
                        heap.decreased(y);
                }
            }
            
            for (unsigned x : am1) 
                heap.erase(x);
                
            if (am1.num_elems() > 1) {
                unsigned_vector mux;
                for (unsigned x : am1)
                    mux.push_back(x);
                if (mux.size() == 2 && mux[0] == negate(mux[1])) 
                    continue;                
                cliques.push_back(mux);
            }
        }
    }


};
