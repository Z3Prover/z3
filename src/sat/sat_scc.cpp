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

    void scc::get_dfs_num(svector<int>& dfs, bool learned) {
        unsigned num_lits = m_solver.num_vars() * 2;
        vector<literal_vector> dag(num_lits);
        svector<bool>          roots(num_lits, true);
        literal_vector todo;
        SASSERT(dfs.size() == num_lits);
        unsigned num_edges = 0;

        // retrieve DAG
        for (unsigned l_idx = 0; l_idx < num_lits; l_idx++) {
            literal u(to_literal(l_idx));
            if (m_solver.was_eliminated(u.var())) 
                continue;
            auto& edges = dag[u.index()];
            for (watched const& w : m_solver.m_watches[l_idx]) {
                if (learned ? w.is_binary_clause() : w.is_binary_unblocked_clause()) {
                    literal v = w.get_literal();
                    roots[v.index()] = false;
                    edges.push_back(v);
                    ++num_edges;
                }
            }
            unsigned sz = edges.size();
            // shuffle vertices to obtain different DAG traversal each time
            if (sz > 1) {
                for (unsigned i = sz; i-- > 0; ) {
                    std::swap(edges[i], edges[m_rand(i+1)]);
                }
            }
        }
        // std::cout << "dag num edges: " << num_edges << "\n";
        // retrieve literals that have no predecessors
        for (unsigned l_idx = 0; l_idx < num_lits; l_idx++) {
            literal u(to_literal(l_idx));
            if (roots[u.index()]) todo.push_back(u);
        }
        // std::cout << "num roots: " << roots.size() << "\n";
        // traverse DAG, annotate nodes with DFS number
        int dfs_num = 0;
        while (!todo.empty()) {
            literal u = todo.back();
            int& d = dfs[u.index()];
            // already visited
            if (d > 0) {
                todo.pop_back();
            }
            // visited as child:
            else if (d < 0) {
                d = -d;
                for (literal v : dag[u.index()]) {
                    if (dfs[v.index()] == 0) {
                        dfs[v.index()] = - d - 1;
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

    bool scc::reduce_tr(svector<int> const& dfs, bool learned) {        
        unsigned idx = 0;
        bool reduced = false;
        for (watch_list & wlist : m_solver.m_watches) {
            literal u = to_literal(idx++);
            watch_list::iterator it     = wlist.begin();
            watch_list::iterator itprev = it;
            watch_list::iterator end    = wlist.end();
            for (; it != end; ++it) {
                watched& w = *it;
                if (learned ? w.is_binary_learned_clause() : w.is_binary_unblocked_clause()) {
                    literal v = w.get_literal();
                    if (dfs[u.index()] + 1 < dfs[v.index()]) {
                        ++m_num_elim_bin;
                        reduced = true;
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
        return reduced;
    }

    bool scc::reduce_tr(bool learned) {
        unsigned num_lits = m_solver.num_vars() * 2;
        svector<int> dfs(num_lits);
        get_dfs_num(dfs, learned);
        return reduce_tr(dfs, learned);
    }

    void scc::reduce_tr() {
        while (reduce_tr(false)) {}
        while (reduce_tr(true)) {}
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
