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
        for (auto& ci : m_clauses) 
            m_alloc.del_clause(ci.m_clause);        
    }

    lbool ddfw::check(unsigned sz, literal const* assumptions, parallel* p) {
        init(sz, assumptions);
        flet<parallel*> _p(m_par, p);
        if (m_plugin)
            check_with_plugin();
        else
            check_without_plugin();
        remove_assumptions();
        log();
        return m_min_sz == 0 ? l_true : l_undef;
    }

    void ddfw::check_without_plugin() {
        while (m_limit.inc() && m_min_sz > 0) {
            if (should_reinit_weights()) do_reinit_weights();
            else if (do_flip<false>());
            else if (should_restart()) do_restart();
            else if (should_parallel_sync()) do_parallel_sync();
            else shift_weights();
        }
    }

    void ddfw::check_with_plugin() {
        m_plugin->init_search();
        m_steps_since_progress = 0;
        unsigned steps = 0;
        while (m_min_sz > 0 && m_steps_since_progress++ <= 1500000) {
            if (should_reinit_weights()) do_reinit_weights();
            else if (steps % 5000 == 0) shift_weights(), m_plugin->on_rescale();
            else if (should_restart()) do_restart(), m_plugin->on_restart();
            else if (do_flip<true>());
            else if (do_literal_flip<true>());
            else if (should_parallel_sync()) do_parallel_sync();
            else shift_weights(), m_plugin->on_rescale();
            ++steps;
        }
        m_plugin->finish_search();
    }

    void ddfw::log() {
        double sec = m_stopwatch.get_current_seconds();        
        double kflips_per_sec = (m_flips - m_last_flips) / (1000.0 * sec);
        if (m_last_flips == 0) {
            IF_VERBOSE(1, verbose_stream() << "(sat.ddfw :unsat :models :kflips/sec  :flips  :restarts  :reinits  :unsat_vars  :shifts";
                       if (m_par) verbose_stream() << "  :par";
                       verbose_stream() << ")\n");
        }
        IF_VERBOSE(1, verbose_stream() << "(sat.ddfw " 
                   << std::setw(07) << m_min_sz 
                   << std::setw(07) << m_models.size()
                   << std::setw(10) << kflips_per_sec
                   << std::setw(10) << m_flips 
                   << std::setw(10) << m_restart_count
                   << std::setw(11) << m_reinit_count
                   << std::setw(13) << m_unsat_vars.size()
                   << std::setw(9) << m_shifts;
                   if (m_par) verbose_stream() << std::setw(10) << m_parsync_count;
                   verbose_stream() << ")\n");
        m_stopwatch.start();
        m_last_flips = m_flips;
    }

    template<bool uses_plugin>
    bool ddfw::do_flip() {
        double reward = 0;
        bool_var v = pick_var<uses_plugin>(reward);
        return apply_flip<uses_plugin>(v, reward);
    }

    template<bool uses_plugin>
    bool ddfw::apply_flip(bool_var v, double reward) {
        if (v == null_bool_var) 
            return false;
        
        if (reward > 0 || (reward == 0 && m_rand(100) <= m_config.m_use_reward_zero_pct)) {
            if (uses_plugin && is_external(v))
                m_plugin->flip(v);
            else
                flip(v);
            if (m_unsat.size() <= m_min_sz) 
                save_best_values();
            return true;
        }
        return false;
    }

    template<bool uses_plugin>
    bool_var ddfw::pick_var(double& r) {
        double sum_pos = 0;
        unsigned n = 1;
        bool_var v0 = null_bool_var;
        for (bool_var v : m_unsat_vars) {
            r = uses_plugin ? plugin_reward(v) : reward(v);
            if (r > 0.0)    
                sum_pos += score(r);            
            else if (r == 0.0 && sum_pos == 0 && (m_rand() % (n++)) == 0) 
                v0 = v;            
        }
        if (sum_pos > 0) {
            double lim_pos = ((double) m_rand() / (1.0 + m_rand.max_value())) * sum_pos;                
            for (bool_var v : m_unsat_vars) {
                r = uses_plugin && is_external(v) ? m_vars[v].m_last_reward : reward(v);
                if (r > 0) {
                    lim_pos -= score(r);
                    if (lim_pos <= 0) 
                        return v;                    
                }
            }
        }
        r = 0;
        if (v0 != null_bool_var) 
            return v0;
        if (m_unsat_vars.empty())
            return null_bool_var;
        return m_unsat_vars.elem_at(m_rand(m_unsat_vars.size()));
    }

    template<bool uses_plugin>
    bool ddfw::do_literal_flip() {
        double reward = 1;
        return apply_flip<uses_plugin>(pick_literal_var<uses_plugin>(), reward);
    }

    /*
    * Pick a random false literal from a satisfied clause such that
    * the literal has zero break count and positive reward.
    */
    template<bool uses_plugin>
    bool_var ddfw::pick_literal_var() {
#if false
        unsigned sz = m_clauses.size();
        unsigned start = rand();
        for (unsigned i = 0; i < 100; ++i) {
            unsigned cl = (i + start) % sz;
            if (m_unsat.contains(cl))
                continue;
            for (auto lit : *m_clauses[cl].m_clause) {
                if (is_true(lit))
                    continue;
                double r = uses_plugin ? plugin_reward(lit.var()) : reward(lit.var());
                if (r < 0)
                    continue;
                //verbose_stream() << "false " << r << " " << lit << "\n";
                return lit.var();
            }
        }
#endif
        return null_bool_var;
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

    /**
     * Remove the last clause that was added
     */
    void ddfw::del() {
        auto& info = m_clauses.back();
        for (literal lit : *info.m_clause)
            m_use_list[lit.index()].pop_back();
        m_alloc.del_clause(info.m_clause);
        m_clauses.pop_back();
        if (m_unsat.contains(m_clauses.size()))
            m_unsat.remove(m_clauses.size());
    }

    void ddfw::add(solver const& s) {
        for (auto& ci : m_clauses) 
            m_alloc.del_clause(ci.m_clause);
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
        for (unsigned i = 0; i < m_assumptions.size(); ++i) 
            add(1, m_assumptions.data() + i);        
    }

    void ddfw::remove_assumptions() {
        if (m_assumptions.empty())
            return;
        for (unsigned i = 0; i < m_assumptions.size(); ++i) 
            del();        
        init(0, nullptr);
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

    void ddfw::reinit(solver& s, bool_vector const& phase) {
        add(s);
        add_assumptions();
        for (unsigned v = 0; v < phase.size(); ++v) {
            value(v) = phase[v];
            reward(v) = 0;
            make_count(v) = 0;
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
            double w = ci.m_weight;
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
            double w = ci.m_weight;
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
        update_reward_avg(v);
    }

    bool ddfw::should_reinit_weights() {
        return m_flips >= m_reinit_next;
    }

    void ddfw::do_reinit_weights() {
        log();

        if (m_reinit_count % 2 == 0) { 
            for (auto& ci : m_clauses) 
                ci.m_weight += 1;                            
        }
        else {
            for (auto& ci : m_clauses) 
                if (ci.is_true()) 
                    ci.m_weight = m_config.m_init_clause_weight;                
                else 
                    ci.m_weight = m_config.m_init_clause_weight + 1;                                       
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
            for (literal lit : c) 
                if (is_true(lit)) 
                    ci.add(lit);                            
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
            if (0 == (m_rand() % (1 + abs(b)))) 
                value(i) = (m_rand() % 2) == 0;            
            else 
                value(i) = bias(i) > 0;            
        }        
    }

    bool ddfw::should_parallel_sync() {
        return m_par != nullptr && m_flips >= m_parsync_next;
    }

    void ddfw::save_priorities() {
        m_probs.reset();
        for (unsigned v = 0; v < num_vars(); ++v) 
            m_probs.push_back(-m_vars[v].m_reward_avg);         
    }

    void ddfw::do_parallel_sync() {
        if (m_par->from_solver(*this)) 
            m_par->to_solver(*this);
        
        ++m_parsync_count;
        m_parsync_next *= 3;
        m_parsync_next /= 2;
    }

    void ddfw::save_model() {
        m_model.reserve(num_vars());
        for (unsigned i = 0; i < num_vars(); ++i) 
            m_model[i] = to_lbool(value(i));
        save_priorities();
        if (m_plugin)
            m_plugin->on_save_model();
    }


    void ddfw::save_best_values() {
        if (m_unsat.size() < m_min_sz) {
            m_steps_since_progress = 0;
            if (m_unsat.size() < 50 || m_min_sz * 10 > m_unsat.size() * 11)
                save_model();
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
        unsigned occs = 0;
        bool contains = m_models.find(h, occs);
        if (!m_models.contains(h)) {
            for (unsigned v = 0; v < num_vars(); ++v)
                bias(v) += value(v) ? 1 : -1;
            if (m_models.size() > m_config.m_max_num_models)
                m_models.erase(m_models.begin()->m_key);
        }
        m_models.insert(h, occs + 1);
        if (occs > 100) {
            m_restart_next = m_flips;            
            m_models.erase(h);
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

    bool ddfw::select_clause(double max_weight, clause_info const& cn, unsigned& n) {
        if (cn.m_num_trues == 0 || cn.m_weight + 1e-5 < max_weight) 
            return false;
        if (cn.m_weight > max_weight) {
            n = 2;
            return true;
        } 
        return (m_rand() % (n++)) == 0;
    }

    unsigned ddfw::select_max_same_sign(unsigned cf_idx) {
        auto& ci = m_clauses[cf_idx];
        unsigned cl = UINT_MAX; // clause pointer to same sign, max weight satisfied clause.
        clause const& c = *ci.m_clause;
        double max_weight = m_init_weight;
        unsigned n = 1;
        for (literal lit : c) {
            for (unsigned cn_idx : use_list(*this, lit)) {
                auto& cn = m_clauses[cn_idx];
                if (select_clause(max_weight, cn, n)) {
                    cl = cn_idx;
                    max_weight = cn.m_weight;
                }
            }
        }
        return cl;
    }

    void ddfw::transfer_weight(unsigned from, unsigned to, double w) {
        auto& cf = m_clauses[to];
        auto& cn = m_clauses[from];
        if (cn.m_weight < w) 
            return;
        cf.m_weight += w;
        cn.m_weight -= w;
        
        for (literal lit : get_clause(to)) 
            inc_reward(lit, w);
        if (cn.m_num_trues == 1) 
            inc_reward(to_literal(cn.m_trues), w);
    }

    unsigned ddfw::select_random_true_clause() {
        unsigned num_clauses = m_clauses.size();
        unsigned rounds = 100 * num_clauses;
        for (unsigned i = 0; i < rounds; ++i) {
            unsigned idx = (m_rand() * m_rand()) % num_clauses;
            auto & cn = m_clauses[idx];
            if (cn.is_true() && cn.m_weight >= m_init_weight) 
                return idx;
        }
        return UINT_MAX;
    }

    // 1% chance to disregard neighbor
    inline bool ddfw::disregard_neighbor() {
        return false; // rand() % 1000 == 0;
    }

    double ddfw::calculate_transfer_weight(double w) {
        return (w > m_init_weight) ? m_init_weight : 1; 
    }

    void ddfw::shift_weights() {
        ++m_shifts;
        for (unsigned to_idx : m_unsat) {
            SASSERT(!m_clauses[to_idx].is_true());
            unsigned from_idx = select_max_same_sign(to_idx);
            if (from_idx == UINT_MAX || disregard_neighbor())
                from_idx = select_random_true_clause();
            if (from_idx == UINT_MAX)
                continue;
            auto & cn = m_clauses[from_idx];
            SASSERT(cn.is_true());
            double w = calculate_transfer_weight(cn.m_weight);
            transfer_weight(from_idx, to_idx, w);
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
            double v_reward = 0;
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
            // SASSERT(reward(v) == v_reward);
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

