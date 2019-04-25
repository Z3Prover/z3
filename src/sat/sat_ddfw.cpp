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
        m_flips = 0; 
        m_shifts = 0;
        while (m_limit.inc() && min_sz > 0) {
            bool_var v = pick_var();
            if (m_reward[v] > 0 || (m_reward[v] == 0 && m_rand(100) <= m_config.m_use_reward_zero_pct)) {
                flip(v);
                if (m_unsat.size() < min_sz) {
                    min_sz = m_unsat.size();
                    IF_VERBOSE(0, verbose_stream() << "flips: " << m_flips << " unsat: " << min_sz << " shifts: " << m_shifts << "\n");
                }
                else if (should_reinit_weights()) {
                    do_reinit_weights(false);
                }
            }
            else {
                shift_weights();
            }
        } 
        if (min_sz == 0) {
            return l_true;
        }
        return l_undef;
    }

    bool_var ddfw::pick_var() {
        if (m_config.m_use_heap) {
            return m_heap.min_value();
        }
        else {
            double lim = (m_rand()/(1.0 + (double)m_rand.max_value())) * (m_reward_sum + m_reward_set.size()); 
            // sorted?
            for (unsigned v : m_reward_set) {
                lim -= m_reward[v] + 1;
                if (lim <= 0) {
                    return v;
                }
            }
            return m_rand(m_reward.size());
        }
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
        unsigned trail_sz = s.init_trail_size();
        for (unsigned i = 0; i < trail_sz; ++i) {
            add(1, s.m_trail.c_ptr() + i);
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

        // initialize reinit toggles
        m_reinit_count = 0;
        m_reinit_inc = 10000;
        m_reinit_next = m_reinit_inc;
        m_reinit_next_reset = 1;
    }

    void ddfw::flip(bool_var v) {
        ++m_flips;
        literal lit = literal(v, !m_values[v]);
        literal nlit = ~lit;
        SASSERT(is_true(lit));
        for (unsigned cls_idx : m_use_list[lit.index()]) {
            clause_info& ci = m_clauses[cls_idx];
            ci.del(lit);
            unsigned w = ci.m_weight;
            // cls becomes false: flip any variable in clause to receive reward w
            switch (ci.m_num_trues) {
            case 0:
                m_unsat.insert(cls_idx);
                for (literal l : get_clause(cls_idx)) {
                    inc_reward(l, w);
                }
                inc_reward(lit, w);
                break;
            case 1:
                dec_reward(to_literal(ci.m_trues), w);
                break;
            default:
                break;
            }
        }
        for (unsigned cls_idx : m_use_list[nlit.index()]) {
            clause_info& ci = m_clauses[cls_idx];             
            unsigned w = ci.m_weight;
            // the clause used to have a single true (pivot) literal, now it has two.
            // Then the previous pivot is no longer penalized for flipping.
            switch (ci.m_num_trues) {
            case 0:
                m_unsat.remove(cls_idx);   
                for (literal l : get_clause(cls_idx)) {
                    dec_reward(l, w);
                }
                dec_reward(nlit, w);
                break;
            case 1:
                inc_reward(to_literal(ci.m_trues), w);
                break;
            default:
                break;
            }
            ci.add(nlit);
        }
        m_values[v] = !m_values[v];
        //DEBUG_CODE(invariant(););
    }

    bool ddfw::should_reinit_weights() {
        return m_flips > m_reinit_next;
    }

    void ddfw::do_reinit_weights(bool force) {
        unsigned np = 0;
        for (int r : m_reward) if (r > 0) np++;
        IF_VERBOSE(0, verbose_stream() 
                   << "reinit weights np: " << np 
                   << " vars: "   << m_reward.size() 
                   << " flips: "  << m_flips 
                   << " shifts: " << m_shifts << "\n");

        if (!force && m_reinit_count < m_reinit_next_reset) {
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
            m_reinit_next_reset += m_reinit_count;
        }
        init_rewards();   
        ++m_reinit_count;
        m_reinit_next += m_reinit_count * m_reinit_inc;
    }

    void ddfw::init_rewards() {
        if (m_config.m_use_heap) {
            m_heap.clear();
            m_heap.reserve(m_reward.size());
            for (unsigned v = 0; v < m_reward.size(); ++v) {
                m_reward[v] = 0;
                m_heap.insert(v);
            }
        }
        else {
            m_reward_set.reset();
            m_reward_sum = 0;
            for (unsigned v = 0; v < m_reward.size(); ++v) {
                m_reward[v] = 0;
                m_reward_set.insert(v);
            }        
        }
        unsigned sz = m_clauses.size();
        for (unsigned i = 0; i < sz; ++i) {
            auto const& ci = m_clauses[i];
            switch (ci.m_num_trues) {
            case 0:
                for (literal lit : get_clause(i)) {
                    inc_reward(lit, ci.m_weight);
                }
                break;
            case 1:
                dec_reward(to_literal(ci.m_trues), ci.m_weight);
                break;
            default:
                break;
            }
        }
    }

    unsigned ddfw::select_max_same_sign(unsigned cf_idx) {
        clause const& c = get_clause(cf_idx);
        unsigned sz = c.size();
        unsigned max_weight = 2;
        unsigned cp = UINT_MAX; // clause pointer to same sign, max weight satisfied clause.
        unsigned cr = UINT_MAX; // clause in reserve
        unsigned n = 1, m = 1;
        for (literal lit : c) {
            auto const& cls = m_use_list[lit.index()];
            for (unsigned cn_idx : cls) {
                auto& cn = m_clauses[cn_idx];
                unsigned wn = cn.m_weight;
                if (cn.is_true()) {
                    if (wn > max_weight) {
                        cp = cn_idx;
                        max_weight = wn;
                        n = 2;
                    }
                    else if (wn == max_weight && (m_rand() % (n++)) == 0) {
                        cp = cn_idx;
                    }
                }
                else if (cp == UINT_MAX && cn_idx != cf_idx && wn >= 2 && (m_rand() % (m++)) == 0) {
                    cr = cn_idx;
                }
            }
        }
        return cp != UINT_MAX ? cp : cr;
    }

    void ddfw::inc_reward(literal lit, int inc) {
        int& r = m_reward[lit.var()];
        r += inc;
        if (m_config.m_use_heap) {
            m_heap.decreased(lit.var());
        }
        else {
            if (r >= 0 && r < inc) {
                m_reward_set.insert(lit.var());
                m_reward_sum += r;
            }
            else if (r >= 0) {
                m_reward_sum += inc;
            }
        }
    }
    
    void ddfw::dec_reward(literal lit, int inc) {
        int& r = m_reward[lit.var()];
        r -= inc;
        if (m_config.m_use_heap) {
            m_heap.increased(lit.var());        
        }
        else {
            if (r < 0 && r + inc >= 0) {
                m_reward_set.remove(lit.var());
                m_reward_sum -= (r + inc);
            }
            else if (r >= 0) {
                m_reward_sum -= inc;
            }
        }
    }

    void ddfw::shift_weights() {
        ++m_shifts;
        unsigned shifted = 0;
        for (unsigned cf_idx : m_unsat) {
            auto& cf = m_clauses[cf_idx];
            SASSERT(!cf.is_true());
            unsigned cn_idx = select_max_same_sign(cf_idx);
            if (cn_idx == UINT_MAX || cf_idx == cn_idx) {
                continue;
            }
            auto& cn = m_clauses[cn_idx];
            if (cn.m_num_trues == 0) {
                continue;
            }
            unsigned wn = cn.m_weight;
            SASSERT(wn >= 2);
            unsigned inc = (wn > 2) ? 2 : 1; 
            SASSERT(wn - inc >= 1);            
            cf.m_weight += inc;
            cn.m_weight -= inc;
            for (literal lit : get_clause(cf_idx)) {
                inc_reward(lit, inc);
                if (m_reward[lit.var()] > 0) shifted++;
            }
            switch (cn.m_num_trues) {
            case 0:
                for (literal lit : get_clause(cn_idx)) {
                    dec_reward(lit, inc);
                }
                break;
            case 1: {
                literal lit = to_literal(cn.m_trues);
                inc_reward(lit, inc);
                break;
            }
            default:
                break;
            }
        }
        if (shifted == 0) {
            do_reinit_weights(true);
        }
        // IF_VERBOSE(0, verbose_stream() << "shift weights " << m_unsat.size() << ": " << shifted << "\n");
    }

    std::ostream& ddfw::display(std::ostream& out) const {
        unsigned num_cls = m_clauses.size();
        for (unsigned i = 0; i < num_cls; ++i) {
            out << get_clause(i) << " ";
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

