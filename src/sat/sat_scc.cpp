/*++
Copyright (c) 2011 Microsoft Corporation

Module Name:

    sat_scc.cpp

Abstract:

    Use binary clauses to compute strongly connected components.

Author:

    Leonardo de Moura (leonardo) 2011-05-26.

Revision History:

--*/
#include "sat/sat_scc.h"
#include "sat/sat_solver.h"
#include "sat/sat_elim_eqs.h"
#include "util/stopwatch.h"
#include "util/trace.h"
#include "sat/sat_scc_params.hpp"

namespace sat {

    scc::scc(solver & s, params_ref const & p):
        m_solver(s) {
        reset_statistics();
        updt_params(p);
    }

    struct frame {
        unsigned  m_lidx;
        unsigned  m_succ_idx;
        bool      m_first;
        watched * m_it;
        watched * m_end;
        frame(unsigned lidx, watched * it, watched * end, unsigned sidx = 0):m_lidx(lidx), m_succ_idx(sidx), m_first(true), m_it(it), m_end(end) {}
    };
    typedef svector<frame> frames;

    struct scc::report {
        scc &     m_scc;
        stopwatch m_watch;
        unsigned  m_num_elim;
        unsigned  m_num_elim_bin;
        report(scc & c):
            m_scc(c),
            m_num_elim(c.m_num_elim),
            m_num_elim_bin(c.m_num_elim_bin) {
            m_watch.start();
        }
        ~report() {
            m_watch.stop();
            unsigned elim_bin = m_scc.m_num_elim_bin - m_num_elim_bin;
            IF_VERBOSE(SAT_VB_LVL, 
                       verbose_stream() << " (sat-scc :elim-vars " << (m_scc.m_num_elim - m_num_elim);
                       if (elim_bin > 0) verbose_stream() << " :elim-bin " << elim_bin;
                       verbose_stream() << mk_stat(m_scc.m_solver)
                       << " :time " << std::fixed << std::setprecision(2) << m_watch.get_seconds() << ")\n";);
        }
    };

    unsigned scc::operator()() {
        if (m_solver.m_inconsistent)
            return 0;
        if (!m_scc)
            return 0;
        CASSERT("scc_bug", m_solver.check_invariant());
        report rpt(*this);
        TRACE("scc", m_solver.display(tout););
        TRACE("scc_details", m_solver.display_watches(tout););
        unsigned_vector index;
        unsigned_vector lowlink;
        unsigned_vector s;
        svector<char>   in_s;
        unsigned num_lits = m_solver.num_vars() * 2;
        index.resize(num_lits, UINT_MAX);
        lowlink.resize(num_lits, UINT_MAX);
        in_s.resize(num_lits, false);
        literal_vector roots, lits;
        roots.resize(m_solver.num_vars(), null_literal);
        unsigned next_index = 0;
        svector<frame>   frames;
        bool_var_vector  to_elim;
        
        for (unsigned l_idx = 0; l_idx < num_lits; l_idx++) {
            if (index[l_idx] != UINT_MAX)
                continue;
            if (m_solver.was_eliminated(to_literal(l_idx).var()))
                continue;
            
            m_solver.checkpoint();

#define NEW_NODE(LIDX) {                                                        \
                index[LIDX]   = next_index;                                     \
                lowlink[LIDX] = next_index;                                     \
                next_index++;                                                   \
                s.push_back(LIDX);                                              \
                in_s[LIDX] = true;                                              \
                watch_list & wlist = m_solver.get_wlist(LIDX);                  \
                frames.push_back(frame(LIDX, wlist.begin(), wlist.end()));      \
            }

            NEW_NODE(l_idx);

            while (!frames.empty()) {
            loop:
                frame & fr = frames.back();
                unsigned l_idx = fr.m_lidx;
                if (!fr.m_first) {
                    SASSERT(fr.m_it->is_binary_clause());
                    // after visiting child
                    literal l2 = fr.m_it->get_literal();
                    unsigned l2_idx = l2.index();
                    SASSERT(index[l2_idx] != UINT_MAX);
                    if (lowlink[l2_idx] < lowlink[l_idx])
                        lowlink[l_idx] = lowlink[l2_idx];
                    fr.m_it++;
                }
                fr.m_first = false;
                while (fr.m_it != fr.m_end) {
                    if (!fr.m_it->is_binary_clause()) {
                        fr.m_it++;
                        continue;
                    }
                    literal l2 = fr.m_it->get_literal();
                    unsigned l2_idx = l2.index();
                    if (index[l2_idx] == UINT_MAX) {
                        NEW_NODE(l2_idx);
                        goto loop;
                    }
                    else if (in_s[l2_idx]) {
                        if (index[l2_idx] < lowlink[l_idx])
                            lowlink[l_idx] = index[l2_idx];
                    }
                    fr.m_it++;
                }
                // visited all successors
                if (lowlink[l_idx] == index[l_idx]) {
                    // found new SCC
                    CTRACE("scc_cycle", s.back() != l_idx, {
                            tout << "cycle: ";
                            unsigned j = s.size() - 1;
                            unsigned l2_idx;
                            do {
                                l2_idx = s[j];
                                j--;
                                tout << to_literal(l2_idx) << " ";
                            } while (l2_idx != l_idx);
                            tout << "\n";
                        });
                    
                    SASSERT(!s.empty());
                    literal l = to_literal(l_idx);
                    bool_var v = l.var();
                    if (roots[v] != null_literal) {
                        // variable was already assigned... just consume stack
                        TRACE("scc_detail", tout << "consuming stack...\n";);
                        unsigned l2_idx;
                        do {
                            l2_idx = s.back();
                            s.pop_back();
                            in_s[l2_idx] = false;
                            SASSERT(roots[to_literal(l2_idx).var()].var() == roots[v].var());
                        } while (l2_idx != l_idx);
                    }
                    else {
                        // check if the SCC has an external variable, and check for conflicts
                        TRACE("scc_detail", tout << "assigning roots...\n";);
                        literal  r = null_literal;
                        unsigned j = s.size() - 1;
                        unsigned l2_idx;
                        do {
                            l2_idx = s[j];
                            j--;
                            if (to_literal(l2_idx) == ~l) {
                                m_solver.set_conflict(justification());
                                return 0;
                            }
                            if (m_solver.is_external(to_literal(l2_idx).var())) {
                                r = to_literal(l2_idx);
                                break;
                            }
                        } while (l2_idx != l_idx);

                        if (r == null_literal) {
                            // SCC does not contain external variable
                            r = to_literal(l_idx);
                        }

                        TRACE("scc_detail", tout << "r: " << r << "\n";);

                        do {
                            l2_idx = s.back();
                            s.pop_back();
                            in_s[l2_idx] = false;
                            literal  l2 = to_literal(l2_idx);
                            bool_var v2 = l2.var();
                            if (roots[v2] == null_literal) {
                                if (l2.sign()) {
                                    roots[v2] = ~r;
                                }
                                else {
                                    roots[v2] = r;
                                }
                                if (v2 != r.var())
                                    to_elim.push_back(v2);
                            }
                        } while (l2_idx != l_idx);
                    }
                }
                frames.pop_back();
            }
        }
        for (unsigned i = 0; i < m_solver.num_vars(); ++i) {
            if (roots[i] == null_literal) {
                roots[i] = literal(i, false);
            }
        }
        TRACE("scc", for (unsigned i = 0; i < roots.size(); i++) { tout << i << " -> " << roots[i] << "\n"; }
              tout << "to_elim: "; for (unsigned i = 0; i < to_elim.size(); i++) tout << to_elim[i] << " "; tout << "\n";);
        m_num_elim += to_elim.size();
        elim_eqs eliminator(m_solver);
        eliminator(roots, to_elim);
        TRACE("scc_detail", m_solver.display(tout););
        CASSERT("scc_bug", m_solver.check_invariant());

        if (m_scc_tr) {
            reduce_tr();
        }
        return to_elim.size();
    }

    // shuffle vertices to obtain different DAG traversal each time
    void scc::shuffle(literal_vector& lits) {
        unsigned sz = lits.size();
        if (sz > 1) {
            for (unsigned i = sz; i-- > 0; ) {
                std::swap(lits[i], lits[m_rand(i+1)]);
            }
        }
    }

    vector<literal_vector> const& scc::get_big(bool learned) {
        unsigned num_lits = m_solver.num_vars() * 2;
        m_dag.reset();
        m_roots.reset();
        m_dag.resize(num_lits, 0);
        m_roots.resize(num_lits, true);
        SASSERT(num_lits == m_dag.size() && num_lits == m_roots.size());
        for (unsigned l_idx = 0; l_idx < num_lits; l_idx++) {
            literal u = to_literal(l_idx);
            if (m_solver.was_eliminated(u.var())) 
                continue;
            auto& edges = m_dag[l_idx];
            for (watched const& w : m_solver.m_watches[l_idx]) {
                if (learned ? w.is_binary_clause() : w.is_binary_unblocked_clause()) {
                    literal v = w.get_literal();
                    m_roots[v.index()] = false;
                    edges.push_back(v);
                }
            }
            shuffle(edges);
        }
        return m_dag;
    }

    void scc::get_dfs_num(bool learned) {
        unsigned num_lits = m_solver.num_vars() * 2;
        SASSERT(m_left.size() == num_lits);
        SASSERT(m_right.size() == num_lits);
        literal_vector todo;
        // retrieve literals that have no predecessors
        for (unsigned l_idx = 0; l_idx < num_lits; l_idx++) {
            literal u(to_literal(l_idx));
            if (m_roots[u.index()]) todo.push_back(u);
        }
        shuffle(todo);
        int dfs_num = 0;
        while (!todo.empty()) {
            literal u = todo.back();
            int& d = m_left[u.index()];
            // already visited
            if (d > 0) {
                if (m_right[u.index()] < 0) {
                    m_right[u.index()] = dfs_num;
                }
                todo.pop_back();
            }
            // visited as child:
            else if (d < 0) {
                d = -d;
                for (literal v : m_dag[u.index()]) {
                    if (m_left[v.index()] == 0) {
                        m_left[v.index()] = - d - 1;
                        m_root[v.index()] = m_root[u.index()];
                        m_parent[v.index()] = u;
                        todo.push_back(v);
                    }
                }
            }
            // new root.
            else {
                d = --dfs_num;
            }
        }
    }

    unsigned scc::reduce_tr(bool learned) {        
        unsigned num_lits = m_solver.num_vars() * 2;
        m_left.reset();
        m_right.reset();
        m_root.reset();
        m_parent.reset();
        m_left.resize(num_lits, 0);
        m_right.resize(num_lits, -1);
        for (unsigned i = 0; i < num_lits; ++i) {
            m_root[i]   = to_literal(i);
            m_parent[i] = to_literal(i);            
        }
        get_dfs_num(learned);
        unsigned idx = 0;
        unsigned elim = m_num_elim_bin;
        for (watch_list & wlist : m_solver.m_watches) {
            literal u = to_literal(idx++);
            watch_list::iterator it     = wlist.begin();
            watch_list::iterator itprev = it;
            watch_list::iterator end    = wlist.end();
            for (; it != end; ++it) {
                watched& w = *it;
                if (learned ? w.is_binary_learned_clause() : w.is_binary_unblocked_clause()) {
                    literal v = w.get_literal();
                    if (m_left[u.index()] + 1 < m_left[v.index()]) {
                        ++m_num_elim_bin;
                    }
                    else {
                        *itprev = *it;
                        itprev++;
                    }
                }
                else {
                    *itprev = *it;
                    itprev++;
                }
            }
            wlist.set_end(itprev);
        }
        return m_num_elim_bin - elim;
    }

    void scc::reduce_tr() {
        unsigned quota = 0, num_reduced = 0;
        while ((num_reduced = reduce_tr(false)) > quota) { quota = std::max(100u, num_reduced / 2); }
        while ((num_reduced = reduce_tr(true)) > quota) { quota = std::max(100u, num_reduced / 2); }
    }

    void scc::collect_statistics(statistics & st) const {
        st.update("elim bool vars", m_num_elim);
        st.update("elim binary", m_num_elim_bin);
    }
    
    void scc::reset_statistics() {
        m_num_elim = 0;
        m_num_elim_bin = 0;
    }

    void scc::updt_params(params_ref const & _p) {
        sat_scc_params p(_p);
        m_scc = p.scc();
        m_scc_tr = p.scc_tr();
    }

    void scc::collect_param_descrs(param_descrs & d) {
        sat_scc_params::collect_param_descrs(d);
    }

};
