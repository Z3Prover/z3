/*++
  Copyright (c) 2019 Microsoft Corporation

  Module Name:

    sat_ddfw.cpp

  Abstract:
   
    DDFW Local search module for clauses

  Author:

    Nikolaj Bjorner, Marijn Heule 2019-4-23
     

  Notes:
  
     http://www.ict.griffith.edu.au/~johnt/publications/CP2006raouf.pdf


  Todo:
  - rephase strategy
  - experiment with backoff schemes for restarts
  - parallel sync
  --*/

#include "util/luby.h"
#include "sat/sat_ddfw.h"
#include "sat/sat_solver.h"
#include "sat/sat_params.hpp"

namespace sat {

    ddfw::~ddfw() {
        for (auto& ci : m_clauses) {
            m_alloc.del_clause(ci.m_clause);
        }
    }


    lbool ddfw::check(unsigned sz, literal const* assumptions, parallel* p) {
        init(sz, assumptions);
        flet<parallel*> _p(m_par, p);
        while (m_limit.inc() && m_min_sz > 0) {
            if (should_reinit_weights()) do_reinit_weights();
            else if (do_flip()) ;
            else if (should_restart()) do_restart();
            else if (should_parallel_sync()) do_parallel_sync();
            else shift_weights();                       
        }
        return m_min_sz == 0 ? l_true : l_undef;
    }

    void ddfw::log() {
        double sec = m_stopwatch.get_current_seconds();        
        double kflips_per_sec = (m_flips - m_last_flips) / (1000.0 * sec);
        if (m_last_flips == 0) {
            IF_VERBOSE(0, verbose_stream() << "(sat.ddfw :unsat :models :kflips/sec  :flips  :restarts  :reinits  :unsat_vars  :shifts";
                       if (m_par) verbose_stream() << "  :par";
                       verbose_stream() << ")\n");
        }
        IF_VERBOSE(0, verbose_stream() << "(sat.ddfw " 
                   << std::setw(07) << m_min_sz 
                   << std::setw(07) << m_models.size()
                   << std::setw(10) << kflips_per_sec
                   << std::setw(10) << m_flips 
                   << std::setw(10) << m_restart_count
                   << std::setw(10) << m_reinit_count
                   << std::setw(10) << m_unsat_vars.size()
                   << std::setw(10) << m_shifts;
                   if (m_par) verbose_stream() << std::setw(10) << m_parsync_count;
                   verbose_stream() << ")\n");
        m_stopwatch.start();
        m_last_flips = m_flips;
    }

    bool ddfw::do_flip() {
        bool_var v = pick_var();
        if (reward(v) > 0 || (reward(v) == 0 && m_rand(100) <= m_config.m_use_reward_zero_pct)) {
            flip(v);
            if (m_unsat.size() <= m_min_sz) save_best_values();
            return true;
        }
        return false;
    }

    bool_var ddfw::pick_var() {
        double sum_pos = 0;
        unsigned n = 1;
        bool_var v0 = null_bool_var;
        for (bool_var v : m_unsat_vars) {
            int r = reward(v);
            if (r > 0) {                
                sum_pos += score(r);
            }
            else if (r == 0 && sum_pos == 0 && (m_rand() % (n++)) == 0) {
                v0 = v;
            }
        }
        if (sum_pos > 0) {
            double lim_pos = ((double) m_rand() / (1.0 + m_rand.max_value())) * sum_pos;                
            for (bool_var v : m_unsat_vars) {
                int r = reward(v);
                if (r > 0) {
                    lim_pos -= score(r);
                    if (lim_pos <= 0) {
                        if (m_par) update_reward_avg(v);
                        return v;
                    }
                }
            }
        }
        if (v0 != null_bool_var) {
            return v0;
        }
        return m_unsat_vars.elem_at(m_rand(m_unsat_vars.size()));
    }

    /**
     * TBD: map reward value to a score, possibly through an exponential function, such as
     * exp(-tau/r), where tau > 0
     */
    double ddfw::mk_score(unsigned r) {
        return r;
    }


    void ddfw::add(unsigned n, literal const* c) {        
        clause* cls = m_alloc.mk_clause(n, c, false);
        unsigned idx = m_clauses.size();
        m_clauses.push_back(clause_info(cls, m_config.m_init_clause_weight));
        for (literal lit : *cls) {
            m_use_list.reserve(2*(lit.var()+1));
            m_vars.reserve(lit.var()+1);
            m_use_list[lit.index()].push_back(idx);
        }
    }

    void ddfw::add(solver const& s) {
        for (auto& ci : m_clauses) {
            m_alloc.del_clause(ci.m_clause);
        }
        m_clauses.reset(); 
        m_use_list.reset();
        m_num_non_binary_clauses = 0;

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
        m_num_non_binary_clauses = s.m_clauses.size();
    }

    void ddfw::add_assumptions() {
        for (unsigned i = 0; i < m_assumptions.size(); ++i) {
            add(1, m_assumptions.data() + i);
        }
    }

    void ddfw::init(unsigned sz, literal const* assumptions) {
        m_assumptions.reset();
        m_assumptions.append(sz, assumptions);
        add_assumptions();
        for (unsigned v = 0; v < num_vars(); ++v) {
            literal lit(v, false), nlit(v, true);
            value(v) = (m_rand() % 2) == 0; // m_use_list[lit.index()].size() >= m_use_list[nlit.index()].size();
        }
        init_clause_data();
        flatten_use_list();

        m_reinit_count = 0;
        m_reinit_next = m_config.m_reinit_base;

        m_restart_count = 0;
        m_restart_next = m_config.m_restart_base*2;

        m_parsync_count = 0;
        m_parsync_next = m_config.m_parsync_base;

        m_min_sz = m_unsat.size();
        m_flips = 0;
        m_last_flips = 0;
        m_shifts = 0;
        m_stopwatch.start();
    }

    void ddfw::reinit(solver& s) {
        add(s);
        add_assumptions();
        if (s.m_best_phase_size > 0) {
            for (unsigned v = 0; v < num_vars(); ++v) {                
                value(v) = s.m_best_phase[v];
                reward(v) = 0;
                make_count(v) = 0;                
            }
        }
        init_clause_data();
        flatten_use_list();
    }

    void ddfw::flatten_use_list() {
        m_use_list_index.reset();
        m_flat_use_list.reset();
        for (auto const& ul : m_use_list) {
            m_use_list_index.push_back(m_flat_use_list.size());
            m_flat_use_list.append(ul);
        }
        m_use_list_index.push_back(m_flat_use_list.size());
    }


    void ddfw::flip(bool_var v) {
        ++m_flips;
        literal lit = literal(v, !value(v));
        literal nlit = ~lit;
        SASSERT(is_true(lit));
        for (unsigned cls_idx : use_list(*this, lit)) {
            clause_info& ci = m_clauses[cls_idx];
            ci.del(lit);
            unsigned w = ci.m_weight;
            // cls becomes false: flip any variable in clause to receive reward w
            switch (ci.m_num_trues) {
            case 0: {
                m_unsat.insert(cls_idx);
                clause const& c = get_clause(cls_idx);
                for (literal l : c) {
                    inc_reward(l, w);
                    inc_make(l);
                }
                inc_reward(lit, w);
                break;
                }
            case 1:
                dec_reward(to_literal(ci.m_trues), w);
                break;
            default:
                break;
            }
        }
        for (unsigned cls_idx : use_list(*this, nlit)) {
            clause_info& ci = m_clauses[cls_idx];             
            unsigned w = ci.m_weight;
            // the clause used to have a single true (pivot) literal, now it has two.
            // Then the previous pivot is no longer penalized for flipping.
            switch (ci.m_num_trues) {
            case 0: {
                m_unsat.remove(cls_idx);   
                clause const& c = get_clause(cls_idx);
                for (literal l : c) {
                    dec_reward(l, w);
                    dec_make(l);
                }
                dec_reward(nlit, w);
                break;
            }
            case 1:
                inc_reward(to_literal(ci.m_trues), w);
                break;
            default:
                break;
            }
            ci.add(nlit);
        }
        value(v) = !value(v);
    }

    bool ddfw::should_reinit_weights() {
        return m_flips >= m_reinit_next;
    }

    void ddfw::do_reinit_weights() {
        log();

        if (m_reinit_count % 2 == 0) { 
            for (auto& ci : m_clauses) {
                ci.m_weight += 1;                
            }
        }
        else {
            for (auto& ci : m_clauses) {
                if (ci.is_true()) {
                    ci.m_weight = m_config.m_init_clause_weight;
                }
                else {
                    ci.m_weight = m_config.m_init_clause_weight + 1;
                }                
            }
        }
        init_clause_data();   
        ++m_reinit_count;
        m_reinit_next += m_reinit_count * m_config.m_reinit_base;
    }

    void ddfw::init_clause_data() {
        for (unsigned v = 0; v < num_vars(); ++v) {
            make_count(v) = 0;
            reward(v) = 0;
        }
        m_unsat_vars.reset();
        m_unsat.reset();
        unsigned sz = m_clauses.size();
        for (unsigned i = 0; i < sz; ++i) {
            auto& ci = m_clauses[i];
            clause const& c = get_clause(i);
            ci.m_trues = 0;
            ci.m_num_trues = 0;
            for (literal lit : c) {
                if (is_true(lit)) {
                    ci.add(lit);
                }
            }
            switch (ci.m_num_trues) {
            case 0:
                for (literal lit : c) {
                    inc_reward(lit, ci.m_weight);
                    inc_make(lit);
                }
                m_unsat.insert(i);
                break;
            case 1:
                dec_reward(to_literal(ci.m_trues), ci.m_weight);
                break;
            default:
                break;
            }
        }
    }

    bool ddfw::should_restart() {
        return m_flips >= m_restart_next;
    }

    void ddfw::do_restart() {        
        reinit_values();
        init_clause_data();
        m_restart_next += m_config.m_restart_base*get_luby(++m_restart_count);
    }

    /**
       \brief the higher the bias, the lower the probability to deviate from the value of the bias 
       during a restart.
        bias  = 0 -> flip truth value with 50%
       |bias| = 1 -> toss coin with 25% probability
       |bias| = 2 -> toss coin with 12.5% probability
       etc
    */
    void ddfw::reinit_values() {
        for (unsigned i = 0; i < num_vars(); ++i) {
            int b = bias(i);
            if (0 == (m_rand() % (1 + abs(b)))) {
                value(i) = (m_rand() % 2) == 0;
            }
            else {
                value(i) = bias(i) > 0;
            }
        }        
    }

    bool ddfw::should_parallel_sync() {
        return m_par != nullptr && m_flips >= m_parsync_next;
    }

    void ddfw::do_parallel_sync() {
        if (m_par->from_solver(*this)) {
            // Sum exp(xi) / exp(a) = Sum exp(xi - a)
            double max_avg = 0;
            for (unsigned v = 0; v < num_vars(); ++v) {
                max_avg = std::max(max_avg, (double)m_vars[v].m_reward_avg);
            }
            double sum = 0;
            for (unsigned v = 0; v < num_vars(); ++v) {
                sum += exp(m_config.m_itau * (m_vars[v].m_reward_avg - max_avg));
            }
            if (sum == 0) {
                sum = 0.01;
            }
            m_probs.reset();
            for (unsigned v = 0; v < num_vars(); ++v) {
                m_probs.push_back(exp(m_config.m_itau * (m_vars[v].m_reward_avg - max_avg)) / sum);
            }
            m_par->to_solver(*this);
        }
        ++m_parsync_count;
        m_parsync_next *= 3;
        m_parsync_next /= 2;
    }

    void ddfw::save_best_values() {
        if (m_unsat.empty()) {
            m_model.reserve(num_vars());
            for (unsigned i = 0; i < num_vars(); ++i) {
                m_model[i] = to_lbool(value(i));
            }
        }
        if (m_unsat.size() < m_min_sz) {
            m_models.reset();
            // skip saving the first model.
            for (unsigned v = 0; v < num_vars(); ++v) {
                int& b = bias(v);
                if (abs(b) > 3) {
                    b = b > 0 ? 3 : -3;
                }
            }
        }
        unsigned h = value_hash();
        if (!m_models.contains(h)) {
            for (unsigned v = 0; v < num_vars(); ++v) {
                bias(v) += value(v) ? 1 : -1;
            }
            m_models.insert(h);
            if (m_models.size() > m_config.m_max_num_models) {                
                m_models.erase(*m_models.begin());
            }
        }
        m_min_sz = m_unsat.size();
    }

    unsigned ddfw::value_hash() const {
        unsigned s0 = 0, s1 = 0;
        for (auto const& vi : m_vars) {
            s0 += vi.m_value;
            s1 += s0;
        }
        return s1;
    }


    /**
       \brief Filter on whether to select a satisfied clause 
       1. with some probability prefer higher weight to lesser weight.
       2. take into account number of trues ?
       3. select multiple clauses instead of just one per clause in unsat.
     */

    bool ddfw::select_clause(unsigned max_weight, unsigned max_trues, clause_info const& cn, unsigned& n) {
        if (cn.m_num_trues == 0 || cn.m_weight < max_weight) {
            return false;
        }
        if (cn.m_weight > max_weight) {
            n = 2;
            return true;
        } 
        return (m_rand() % (n++)) == 0;
    }

    unsigned ddfw::select_max_same_sign(unsigned cf_idx) {
        clause const& c = get_clause(cf_idx);
        unsigned max_weight = 2;
        unsigned max_trues = 0;
        unsigned cl = UINT_MAX; // clause pointer to same sign, max weight satisfied clause.
        unsigned n = 1;
        for (literal lit : c) {
            for (unsigned cn_idx : use_list(*this, lit)) {
                auto& cn = m_clauses[cn_idx];
                if (select_clause(max_weight, max_trues, cn, n)) {
                    cl = cn_idx;
                    max_weight = cn.m_weight;
                    max_trues = cn.m_num_trues;
                }
            }
        }
        return cl;
    }

    void ddfw::shift_weights() {
        ++m_shifts;
        for (unsigned cf_idx : m_unsat) {
            auto& cf = m_clauses[cf_idx];
            SASSERT(!cf.is_true());
            unsigned cn_idx = select_max_same_sign(cf_idx);
            while (cn_idx == UINT_MAX) {
                unsigned idx = (m_rand() * m_rand()) % m_clauses.size();
                auto & cn = m_clauses[idx];
                if (cn.is_true() && cn.m_weight >= 2) {
                    cn_idx = idx;
                }
            }
            auto & cn = m_clauses[cn_idx];
            SASSERT(cn.is_true());
            unsigned wn = cn.m_weight;
            SASSERT(wn >= 2);
            unsigned inc = (wn > 2) ? 2 : 1; 
            SASSERT(wn - inc >= 1);            
            cf.m_weight += inc;
            cn.m_weight -= inc;
            for (literal lit : get_clause(cf_idx)) {
                inc_reward(lit, inc);
            }
            if (cn.m_num_trues == 1) {
                inc_reward(to_literal(cn.m_trues), inc);
            }
        }
        // DEBUG_CODE(invariant(););
    }

    std::ostream& ddfw::display(std::ostream& out) const {
        unsigned num_cls = m_clauses.size();
        for (unsigned i = 0; i < num_cls; ++i) {
            out << get_clause(i) << " ";
            auto const& ci = m_clauses[i];
            out << ci.m_num_trues << " " << ci.m_weight << "\n";
        }
        for (unsigned v = 0; v < num_vars(); ++v) {
            out << v << ": " << reward(v) << "\n";
        }
        out << "unsat vars: ";
        for (bool_var v : m_unsat_vars) {
            out << v << " ";
        }
        out << "\n";
        return out;
    }

    void ddfw::invariant() {
        // every variable in unsat vars is in a false clause.
        for (bool_var v : m_unsat_vars) {
            bool found = false;
            for (unsigned cl : m_unsat) {
                for (literal lit : get_clause(cl)) {
                    if (lit.var() == v) { found = true; break; }
                }
                if (found) break;
            }
            if (!found) IF_VERBOSE(0, verbose_stream() << "unsat var not found: " << v << "\n"; );
            VERIFY(found);
        }
        for (unsigned v = 0; v < num_vars(); ++v) {
            int v_reward = 0;
            literal lit(v, !value(v));
            for (unsigned j : m_use_list[lit.index()]) {
                clause_info const& ci = m_clauses[j];
                if (ci.m_num_trues == 1) {
                    SASSERT(lit == to_literal(ci.m_trues));
                    v_reward -= ci.m_weight;
                }
            }
            for (unsigned j : m_use_list[(~lit).index()]) {
                clause_info const& ci = m_clauses[j];
                if (ci.m_num_trues == 0) {
                    v_reward += ci.m_weight;
                }                
            }
            IF_VERBOSE(0, if (v_reward != reward(v)) verbose_stream() << v << " " << v_reward << " " << reward(v) << "\n");
            SASSERT(reward(v) == v_reward);
        }
        DEBUG_CODE(
            for (auto const& ci : m_clauses) {
                SASSERT(ci.m_weight > 0);
            }
            for (unsigned i = 0; i < m_clauses.size(); ++i) {
                bool found = false;
                for (literal lit : get_clause(i)) {
                    if (is_true(lit)) found = true;
                }
                SASSERT(found == !m_unsat.contains(i));
            }
            // every variable in a false clause is in unsat vars
            for (unsigned cl : m_unsat) {
                for (literal lit : get_clause(cl)) {
                    SASSERT(m_unsat_vars.contains(lit.var()));
                }
            });
    }

    void ddfw::updt_params(params_ref const& _p) {
        sat_params p(_p);
        m_config.m_init_clause_weight = p.ddfw_init_clause_weight();
        m_config.m_use_reward_zero_pct = p.ddfw_use_reward_pct();
        m_config.m_reinit_base = p.ddfw_reinit_base();
        m_config.m_restart_base = p.ddfw_restart_base();        
    }
    
}

