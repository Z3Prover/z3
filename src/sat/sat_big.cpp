/*++
Copyright (c) 2011 Microsoft Corporation

Module Name:

    sat_big.cpp

Abstract:

    binary implication graph structure.

Author:

    Nikolaj Bjorner (nbjorner) 2017-12-13.

Revision History:

--*/
#include "sat/sat_big.h"
#include "sat/sat_solver.h"

namespace sat {

    big::big(random_gen& rand): 
        m_rand(rand) {
    }

    void big::init(solver& s, bool learned) {
        init_adding_edges(s.num_vars(), learned);
        unsigned num_lits = m_num_vars * 2;
        literal_vector lits, r;
        SASSERT(num_lits == m_dag.size() && num_lits == m_roots.size());
        size_t_map<bool> seen_idx;
        for (unsigned l_idx = 0; l_idx < num_lits; l_idx++) {
            literal u = to_literal(l_idx);
            if (s.was_eliminated(u.var())) 
                continue;
            auto& edges = m_dag[l_idx];
            for (watched const& w : s.get_wlist(l_idx)) {
                if (learned ? w.is_binary_clause() : w.is_binary_non_learned_clause()) {
                    literal v = w.get_literal();
                    m_roots[v.index()] = false;
                    edges.push_back(v);
                }
#if 1
                if (w.is_ext_constraint() && 
                    s.m_ext && 
                    learned && 
                    !seen_idx.contains(w.get_ext_constraint_idx()) &&
                    s.m_ext->is_extended_binary(w.get_ext_constraint_idx(), r)) {
                    seen_idx.insert(w.get_ext_constraint_idx(), true);
                    for (unsigned i = 0; i < r.size(); ++i) {
                        literal u = r[i]; 
                        for (unsigned j = i + 1; j < r.size(); ++j) {
                            // add r[i] -> ~r[j]
                            literal v = ~r[j];
                            m_roots[v.index()] = false;
                            m_dag[u.index()].push_back(v);
                            // add r[j] -> ~r[i]
                            v.neg();
                            u.neg();
                            m_roots[u.index()] = false;
                            m_dag[v.index()].push_back(u);
                        }
                    }
                }
#endif
            }
        }
        done_adding_edges();
    }

    void big::reinit() {
        done_adding_edges();
    }

    void big::init_adding_edges(unsigned num_vars, bool learned) {
        m_learned = learned;
        m_num_vars = num_vars;
        unsigned num_lits = m_num_vars * 2;
        m_dag.reset();
        m_roots.reset();
        m_dag.resize(num_lits, 0);
        m_roots.resize(num_lits, true);
    }

    void big::add_edge(literal u, literal v) {
        m_dag[u.index()].push_back(v);
    }

    void big::done_adding_edges() {
        for (auto& edges : m_dag) {
            shuffle<literal>(edges.size(), edges.c_ptr(), m_rand);
        }
        init_dfs_num();
    }


    struct big::pframe {
        literal m_parent;
        literal m_child;
        pframe(literal p, literal c):
            m_parent(p), m_child(c) {}
        literal child() const { return m_child; }
        literal parent() const { return m_parent; }
    };

    void big::init_dfs_num() {
        unsigned num_lits = m_num_vars * 2;
        m_left.reset();
        m_right.reset();
        m_root.reset();
        m_parent.reset();
        m_left.resize(num_lits, 0);
        m_right.resize(num_lits, -1);
        m_root.resize(num_lits, null_literal);
        m_parent.resize(num_lits, null_literal);
        for (unsigned i = 0; i < num_lits; ++i) {
            m_root[i]   = to_literal(i);
            m_parent[i] = to_literal(i);            
        }
        svector<pframe> todo;
        // retrieve literals that have no predecessors
        for (unsigned l_idx = 0; l_idx < num_lits; l_idx++) {
            literal u(to_literal(l_idx));
            if (m_roots[u.index()]) {
                todo.push_back(pframe(null_literal, u));
            }
        }
        shuffle<pframe>(todo.size(), todo.c_ptr(), m_rand);
        int dfs_num = 0;
        while (!todo.empty()) {
            literal u = todo.back().child();
            if (m_left[u.index()] > 0) {
                // already visited
                if (m_right[u.index()] < 0) {
                    m_right[u.index()] = ++dfs_num;
                }
                todo.pop_back();
            }
            else {
                SASSERT(m_left[u.index()] == 0);
                m_left[u.index()] = ++dfs_num;
                literal p = todo.back().parent();
                if (p != null_literal) {
                    m_root[u.index()] = m_root[p.index()];
                    m_parent[u.index()] = p;
                }
                for (literal v : m_dag[u.index()]) {
                    if (m_left[v.index()] == 0) {
                        todo.push_back(pframe(u, v));
                    }
                }
            }
        }
        for (unsigned i = 0; i < num_lits; ++i) {
            if (m_right[i] < 0) {
                VERIFY(m_left[i] == 0);
                m_left[i]  = ++dfs_num;
                m_right[i] = ++dfs_num;
            }
        }
        DEBUG_CODE(for (unsigned i = 0; i < num_lits; ++i) { VERIFY(m_left[i] < m_right[i]);});
    }

    unsigned big::reduce_tr(solver& s) {
        unsigned num_lits = s.num_vars() * 2;
        unsigned idx = 0;
        unsigned elim = 0;
        for (watch_list & wlist : s.m_watches) {
            literal u = to_literal(idx++);
            watch_list::iterator it     = wlist.begin();
            watch_list::iterator itprev = it;
            watch_list::iterator end    = wlist.end();
            for (; it != end; ++it) {
                watched& w = *it;
                if (learned() ? w.is_binary_learned_clause() : w.is_binary_clause()) {
                    literal v = w.get_literal();
                    if (reaches(u, v) && u != get_parent(v)) {
                        ++elim;
                        // could turn non-learned non-binary tautology into learned binary.
                        s.get_wlist(~v).erase(watched(~u, w.is_learned()));
                        continue;
                    }
                }
                *itprev = *it;
                itprev++;
            }
            wlist.set_end(itprev);
        }
        return elim;
    }

    void big::display(std::ostream& out) const {
        unsigned idx = 0;
        for (auto& next : m_dag) {
            if (!next.empty()) {
                out << to_literal(idx) << " : " << m_left[idx] << ":" << m_right[idx] << " -> " << next << "\n";
            }
            ++idx;
        }
    }



};
