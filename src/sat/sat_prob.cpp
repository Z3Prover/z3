/*++
  Copyright (c) 2019 Microsoft Corporation

  Module Name:

    sat_prob.cpp

  Abstract:
   
    PROB Local search module for clauses

  Author:

    Nikolaj Bjorner 2019-4-23

  Notes:
  
  --*/

#include "sat/sat_prob.h"
#include "sat/sat_solver.h"
#include "util/luby.h"

namespace sat {

    prob::~prob() {
        for (clause* cp : m_clause_db) {
            m_alloc.del_clause(cp);
        }
    }

    lbool prob::check(unsigned n, literal const* assumptions, parallel* p) {
        VERIFY(n == 0);
        init();
        while (m_limit.inc() && m_best_min_unsat > 0) {
            if (should_restart()) do_restart();
            else flip();
        } 
        if (m_best_min_unsat == 0) {
            return l_true;
        }
        return l_undef;
    }

    void prob::flip() {
        bool_var v = pick_var();
        flip(v);
        if (m_unsat.size() < m_best_min_unsat) {
            save_best_values();
        }
    }

    bool_var prob::pick_var() {
        unsigned cls_idx = m_unsat.elem_at(m_rand() % m_unsat.size());
        double sum_prob = 0;
        unsigned i = 0;        
        clause const& c = get_clause(cls_idx);
        for (literal lit : c) {
            double prob = m_prob_break[m_breaks[lit.var()]];
            m_probs[i++] = prob;
            sum_prob += prob;
        }
        double lim = sum_prob * ((double)m_rand() / m_rand.max_value());
        do {
            lim -= m_probs[--i];
        }
        while (lim >= 0 && i > 0);
        return c[i].var();
    }

    void prob::flip(bool_var v) {
        ++m_flips;
        literal lit = literal(v, !m_values[v]);
        literal nlit = ~lit;
        SASSERT(is_true(lit));
        SASSERT(lit.index() < m_use_list.size());
        SASSERT(m_use_list_index.size() == m_use_list.size() + 1);
        for (unsigned cls_idx : use_list(*this, lit)) {
            clause_info& ci = m_clauses[cls_idx];
            ci.del(lit);
            switch (ci.m_num_trues) {
            case 0:
                m_unsat.insert(cls_idx);
                dec_break(lit);
                break;
            case 1:
                inc_break(to_literal(ci.m_trues));
                break;
            default:
                break;
            }
        }
        for (unsigned cls_idx : use_list(*this, nlit)) {
            clause_info& ci = m_clauses[cls_idx];         
            switch (ci.m_num_trues) {
            case 0:
                m_unsat.remove(cls_idx);   
                inc_break(nlit);
                break;
            case 1:
                dec_break(to_literal(ci.m_trues));
                break;
            default:
                break;
            }
            ci.add(nlit);
        }
        m_values[v] = !m_values[v];
    }

    void prob::add(unsigned n, literal const* c) {        
        clause* cls = m_alloc.mk_clause(n, c, false);
        unsigned idx = m_clause_db.size();
        m_clause_db.push_back(cls);
        m_clauses.push_back(clause_info());
        for (literal lit : *cls) {
            m_values.reserve(lit.var()+1);
            m_breaks.reserve(lit.var()+1);
            m_use_list.reserve((1+lit.var())*2);
            m_use_list[lit.index()].push_back(idx);
        }
        m_probs.reserve(n+1);
    }

    void prob::add(solver const& s) {
        m_values.reserve(s.num_vars(), false);
        unsigned trail_sz = s.init_trail_size();
        for (unsigned i = 0; i < trail_sz; ++i) {
            add(1, s.m_trail.data() + i);
        }
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

    void prob::save_best_values() {
        m_best_min_unsat = m_unsat.size();
        m_best_values.reserve(m_values.size());
        m_model.reserve(m_values.size());
        for (unsigned i = 0; i < m_values.size(); ++i) {
            m_best_values[i] = m_values[i];
            m_model[i] = to_lbool(m_values[i]);
        }
    }
    
    void prob::flatten_use_list() {
        m_use_list_index.reset();
        m_flat_use_list.reset();
        for (auto const& ul : m_use_list) {
            m_use_list_index.push_back(m_flat_use_list.size());
            m_flat_use_list.append(ul);
        }
        m_use_list_index.push_back(m_flat_use_list.size());
    }

    void prob::init_clauses() {
        for (unsigned& b : m_breaks) {
            b = 0;
        }
        m_unsat.reset();
        for (unsigned i = 0; i < m_clauses.size(); ++i) {
            clause_info& ci = m_clauses[i];
            ci.m_num_trues = 0;
            ci.m_trues = 0;
            clause const& c = get_clause(i);
            for (literal lit : c) {
                if (is_true(lit)) {
                    ci.add(lit);
                }
            }
            switch (ci.m_num_trues) {
            case 0:
                m_unsat.insert(i);
                break;
            case 1:
                inc_break(to_literal(ci.m_trues));
                break;
            default:
                break;
            }
        }
    }

    void prob::auto_config() {
        unsigned max_len = 0;
        for (clause* cp : m_clause_db) {
            max_len = std::max(max_len, cp->size());
        }
        // ProbSat magic constants
        switch (max_len) {
        case 0: case 1: case 2: case 3: m_config.m_cb = 2.5; break;
        case 4: m_config.m_cb = 2.85; break;
        case 5: m_config.m_cb = 3.7; break;
        case 6: m_config.m_cb = 5.1; break;
        default: m_config.m_cb = 5.4; break;
        }

        unsigned max_num_occ = 0;
        for (auto const& ul : m_use_list) {
            max_num_occ = std::max(max_num_occ, ul.size());
        }
        // vodoo from prob-sat
        m_prob_break.reserve(max_num_occ+1);
        for (int i = 0; i <= static_cast<int>(max_num_occ); ++i) {
            m_prob_break[i] = pow(m_config.m_cb, -i);
        }
    }

    void prob::log() {
        double sec = m_stopwatch.get_current_seconds();
        double kflips_per_sec = m_flips / (1000.0 * sec);
        IF_VERBOSE(0, verbose_stream() 
                   << sec << " sec. "
                   << (m_flips/1000)   << " kflips " 
                   << m_best_min_unsat << " unsat " 
                   << kflips_per_sec   << " kflips/sec "
                   << m_restart_count  << " restarts\n");
    }

    void prob::init() {
        flatten_use_list();
        init_random_values();
        init_clauses();
        auto_config();
        save_best_values();
        m_restart_count = 1;
        m_flips = 0; 
        m_next_restart = m_config.m_restart_offset;
        m_stopwatch.start();
    }

    void prob::init_random_values() {
        for (unsigned v = 0; v < m_values.size(); ++v) {
            m_values[v] = (m_rand() % 2 == 0);
        }
    }

    void prob::init_best_values() {
        for (unsigned v = 0; v < m_values.size(); ++v) {
            m_values[v] = m_best_values[v];
        }
    }

    void prob::init_near_best_values() {
        for (unsigned v = 0; v < m_values.size(); ++v) {
            if (m_rand(100) < m_config.m_prob_random_init) {
                m_values[v] = !m_best_values[v];
            }
            else {
                m_values[v] = m_best_values[v];
            }
        }
    }

    void prob::do_restart() {
        reinit_values();
        init_clauses();
        m_next_restart += m_config.m_restart_offset*get_luby(m_restart_count++);
        log();
    }

    bool prob::should_restart() {
        return m_flips >= m_next_restart;
    }

    void prob::reinit_values() {
        init_near_best_values();        
    }

    std::ostream& prob::display(std::ostream& out) const {
        unsigned num_cls = m_clauses.size();
        for (unsigned i = 0; i < num_cls; ++i) {
            out << get_clause(i) << " ";
            auto const& ci = m_clauses[i];
            out << ci.m_num_trues << "\n";
        }
        return out;
    }

    void prob::invariant() {

    }

}

