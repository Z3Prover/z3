/*++
  Copyright (c) 2019 Microsoft Corporation

  Module Name:

    sat_ddfw.cpp

  Abstract:
   
    DDFW Local search module for clauses

  Author:

    Nikolaj Bjorner 2019-4-23

  Notes:
  
     http://www.ict.griffith.edu.au/~johnt/publications/CP2006raouf.pdf

  --*/

#include "sat/sat_ddfw.h"
#include "sat/sat_solver.h"

namespace sat {

    ddfw::~ddfw() {
        for (clause* cp : m_clause_db) {
            m_alloc.del_clause(cp);
        }
    }

    lbool ddfw::check() {
        init();
        unsigned min_sz = m_unsat.size();
        unsigned flips = 0, shifts = 0;
        while (!m_unsat.empty() && m_limit.inc()) {
            // display(verbose_stream());
            bool_var v = m_heap.min_value();
            IF_VERBOSE(0, verbose_stream() << "reward: " << m_reward[v] << "\n");
            if (m_reward[v] > 0 || m_reward[v] == 0 && m_rand(100) <= 15) {
                IF_VERBOSE(0, verbose_stream() << "flip " << v << " " << m_reward[v] << "\n");
                flip(v);
                ++flips;
                if (m_unsat.size() < min_sz) {
                    m_plateau_counter = 0;
                    min_sz = m_unsat.size();
                    IF_VERBOSE(1, verbose_stream() << "flips: " << flips << " unsat: " << min_sz << " shifts: " << shifts << "\n");
                    if (min_sz == 0) {
                        return l_true;
                    }
                }
                else if (should_reinit_weights()) {
                    do_reinit_weights();
                }
            }
            else {
                ++shifts;
                shift_weights();
            }
        } 
        return l_undef;
    }

    void ddfw::add(unsigned n, literal const* c) {        
        clause* cls = m_alloc.mk_clause(n, c, false);
        unsigned idx = m_clause_db.size();
        m_clause_db.push_back(cls);
        m_clauses.push_back(clause_info());
        for (literal lit : *cls) {
            m_use_list.reserve(lit.index()+1);
            m_reward.reserve(lit.var()+1, 0);
            m_use_list[lit.index()].push_back(idx);
        }
    }

    void ddfw::add(solver const& s) {
        unsigned sz = s.m_watches.size();
        for (unsigned l_idx = 0; l_idx < sz; ++l_idx) {
            literal l1 = ~to_literal(l_idx);
            watch_list const & wlist = s.m_watches[l_idx];
            for (watched const& w : wlist) {
                if (!w.is_binary_non_learned_clause())
                    continue;
                literal l2 = w.get_literal();
                if (l1.index() > l2.index()) 
                    continue;
                literal ls[2] = { l1, l2 };
                add(2, ls);
            }
        }
        for (clause* c : s.m_clauses) {
            add(c->size(), c->begin());
        }        
    }


    void ddfw::init() {
        m_values.reserve(m_reward.size());
        for (unsigned v = 0; v < m_reward.size(); ++v) {
            m_values[v] = (m_rand() % 2 == 0);
        }
        for (unsigned i = 0; i < m_clauses.size(); ++i) {
            clause_info& info = m_clauses[i];
            info.m_num_trues = 0;
            info.m_weight = 2;
            info.m_trues = 0;
            for (literal lit : get_clause(i)) {
                if (is_true(lit)) {
                    info.add(lit);
                }
            }
            if (!info.is_true()) {
                m_unsat.insert(i);
            }
        }
        init_rewards();

        // initialize plateau toggles
        m_plateau_counter = 0;
        m_plateau_inc = 1 + (m_values.size()/10);
        m_plateau_lim = 2*m_plateau_inc;
        m_reinit_phase = false;
    }

    void ddfw::flip(bool_var v) {
        literal lit = literal(v, !m_values[v]);
        SASSERT(is_true(lit));
        for (unsigned cls_idx : m_use_list[lit.index()]) {
            clause_info& ci = m_clauses[cls_idx];
            ci.del(lit);
            unsigned w = ci.m_weight;
            IF_VERBOSE(0, verbose_stream() << "del: " << get_clause(cls_idx) << " " << w << "\n");
            // cls becomes false: flip any variable in clause to receive reward w
            if (ci.m_num_trues == 0) {
                m_unsat.insert(cls_idx);
                clause const& c = get_clause(cls_idx);
                for (literal l : c) {
                    m_reward[l.var()] += w;
                    m_heap.increased(l.var());
                }
                m_reward[lit.var()] += w;
                m_heap.increased(lit.var());
            }
            // cls has single true literal, set the penalty of flipping l to w.
            if (ci.m_num_trues == 1) {
                literal l = to_literal(ci.m_trues);
                IF_VERBOSE(0, verbose_stream() << "pivot " << l << "\n");
                SASSERT(is_true(l));
                m_reward[l.var()] -= w;
                m_heap.decreased(l.var());
            }
        }
        lit.neg();
        m_values[v] = !m_values[v];
        for (unsigned cls_idx : m_use_list[lit.index()]) {
            clause_info& ci = m_clauses[cls_idx];             
            unsigned w = ci.m_weight;
            // the clause used to have a single true (pivot) literal, now it has two.
            // Then the previous pivot is no longer penalized for flipping.
            if (ci.m_num_trues == 1) {
                literal l = to_literal(ci.m_trues);
                m_reward[l.var()] += w;
                m_heap.increased(l.var());
            }
            ci.add(lit);
            IF_VERBOSE(0, verbose_stream() << "add: " << get_clause(cls_idx) << " " << ci.m_weight << "\n");
            if (ci.m_num_trues == 1) {
                m_unsat.remove(cls_idx);   
                clause const& c = get_clause(cls_idx);
                for (literal l : c) {
                    m_reward[l.var()] -= w;
                    m_heap.decreased(l.var());
                }
                m_reward[lit.var()] -= w;
                m_heap.decreased(lit.var());
            }
        }
        DEBUG_CODE(invariant(););
    }

    bool ddfw::should_reinit_weights() {
        m_plateau_counter += 1;
        return m_plateau_counter > m_plateau_lim;
    }

    void ddfw::do_reinit_weights() {
        IF_VERBOSE(0, verbose_stream() << "reinit weights\n");
        m_plateau_counter = 0;
        m_plateau_lim += m_plateau_inc;
        if (m_reinit_phase) {
            for (auto& ci : m_clauses) {
                ci.m_weight += 1;                
            }
        }
        else {
            for (auto& ci : m_clauses) {
                if (ci.is_true()) {
                    ci.m_weight = 2;
                }
                else {
                    ci.m_weight = 3;
                }                
            }
        }
        init_rewards();       
        m_reinit_phase = !m_reinit_phase;
    }

    void ddfw::init_rewards() {
        m_heap.clear();
        for (int& r : m_reward) {
            r = 0;
        }        
        unsigned sz = m_clauses.size();
        for (unsigned i = 0; i < sz; ++i) {
            auto const& ci = m_clauses[i];
            clause const& c = *m_clause_db[i];
            if (!ci.is_true()) {
                for (literal lit : c) {
                    m_reward[lit.var()] += ci.m_weight;
                }
            }
            if (ci.m_num_trues == 1) {
                literal lit = to_literal(ci.m_trues);
                m_reward[lit.var()] -= ci.m_weight;
            }
        }
        m_heap.reserve(m_reward.size());
        for (unsigned v = 0; v < m_reward.size(); ++v) {
            m_heap.insert(v);
        }
        DEBUG_CODE(invariant(););
    }

    unsigned ddfw::select_max_same_sign(clause const& c) {
        unsigned start = m_rand();
        unsigned sz = c.size();
        unsigned max_weight = 1;
        unsigned cp = UINT_MAX; // clause pointer to same sign, max weight satisfied clause.
        unsigned cr = UINT_MAX; // clause in reserve
        unsigned n = 1, m = 1;
        // IF_VERBOSE(0, verbose_stream() << "clause size " << sz << "\n");
        for (unsigned i = 0; i < sz; ++i) {
            literal lit = c[(start + i) % sz];
            auto const& cls = m_use_list[lit.index()];
            // IF_VERBOSE(0, verbose_stream() << "use list size: " << cls.size() << " " << cp << " " << cr << "\n");
            unsigned st = m_rand();
            unsigned n_cls = cls.size();
            for (unsigned j = 0; j < n_cls; ++j) {
                unsigned cn_idx = cls[(st + j) % n_cls];
                auto& cn = m_clauses[cn_idx];
                unsigned wn = cn.m_weight;
                // IF_VERBOSE(0, verbose_stream() << cn_idx << " " << cn.is_true() << " weight: " << wn << "\n");
                if (cn.is_true()) {
                    if (wn > max_weight) {
                        cp = cn_idx;
                        max_weight = wn;
                        n = 1;
                    }
                    else if (wn == max_weight) {
                        ++n;
                        if ((m_rand() % n) == 0) {
                            cp = cn_idx;
                        }
                    }
                }
                else if (cp == UINT_MAX && wn >= 2) {
                    if ((m_rand() % m) == 0) {
                        cr = cn_idx;
                    }
                    ++m;
                }
            }
        }
        SASSERT(cp != UINT_MAX || cr != UINT_MAX);
        return cp != UINT_MAX ? cp : cr;
    }

    void ddfw::shift_weights() {
        IF_VERBOSE(0, verbose_stream() << "shift weights\n");
        for (unsigned cf_idx : m_unsat) {
            auto& cf = m_clauses[cf_idx];
            SASSERT(!cf.is_true());
            unsigned cn_idx = select_max_same_sign(get_clause(cf_idx));
            auto& cn = m_clauses[cn_idx];
            unsigned wn = cn.m_weight;
            SASSERT(wn >= 2);
            unsigned inc = (wn > 2) ? 2 : 1; 
            SASSERT(wn - inc >= 1);
            cf.m_weight += inc;
            cn.m_weight -= inc;
            for (literal lit : get_clause(cf_idx)) {
                m_reward[lit.var()] += inc;
                m_heap.increased(lit.var());
            }
            if (cn.m_num_trues == 0) {
                for (literal lit : get_clause(cn_idx)) {
                    m_reward[lit.var()] -= inc;
                    m_heap.decreased(lit.var());
                }
            }
            if (cn.m_num_trues == 1) {
                literal lit = to_literal(cn.m_trues);
                m_reward[lit.var()] += inc;
                m_heap.increased(lit.var());                
            }
        }
    }

    std::ostream& ddfw::display(std::ostream& out) const {
        unsigned num_cls = m_clauses.size();
        for (unsigned i = 0; i < num_cls; ++i) {
            out << *m_clause_db[i] << " ";
            auto const& ci = m_clauses[i];
            out << ci.m_num_trues << " " << ci.m_weight << "\n";
        }
        unsigned num_vars = m_reward.size();
        for (unsigned v = 0; v < num_vars; ++v) {
            out << v << ": " << m_reward[v] << "\n";
        }
        return out;
    }

    void ddfw::invariant() {
        IF_VERBOSE(0, verbose_stream() << "invariant\n");
        unsigned num_vars = m_reward.size();
        for (unsigned v = 0; v < num_vars; ++v) {
            int reward = 0;
            literal lit(v, !m_values[v]);
            for (unsigned j : m_use_list[lit.index()]) {
                clause_info const& ci = m_clauses[j];
                if (ci.m_num_trues == 1) {
                    reward -= ci.m_weight;
                }
            }
            for (unsigned j : m_use_list[(~lit).index()]) {
                clause_info const& ci = m_clauses[j];
                if (ci.m_num_trues == 0) {
                    reward += ci.m_weight;
                }                
            }
            IF_VERBOSE(0, if (reward != m_reward[v]) verbose_stream() << v << " " << reward << " " << m_reward[v] << "\n");
            SASSERT(m_reward[v] == reward);
        }
        for (auto const& ci : m_clauses) {
            SASSERT(ci.m_weight > 0);
        }
    }

}

