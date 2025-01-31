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
#include "util/trace.h"
#include "ast/sls/sat_ddfw.h"
#include "params/sat_params.hpp"


namespace sat {

    ddfw::~ddfw() {
    }

    lbool ddfw::check(unsigned sz, literal const* assumptions) {
        init(sz, assumptions);   
        if (m_plugin)
            check_with_plugin();
        else
            check_without_plugin();
        remove_assumptions();
        log();
        return m_min_sz == 0 && m_limit.inc()  ? m_last_result : l_undef;
    }

    void ddfw::check_without_plugin() {
        while (m_limit.inc() && m_min_sz > 0) {
            if (should_reinit_weights()) do_reinit_weights();
            else if (do_flip());
            else if (should_restart()) do_restart();
            else if (m_parallel_sync && m_parallel_sync());
            else shift_weights();
        }
    }

    void ddfw::check_with_plugin() {
        unsigned steps = 0;
        if (m_min_sz <= m_unsat.size())
            save_best_values();
        
        try {
            while (m_min_sz > 0 && m_limit.inc()) {
                if (should_reinit_weights()) do_reinit_weights();
                else if (steps % 5000 == 0) shift_weights(), m_plugin->on_rescale();
                else if (should_restart()) do_restart(), m_plugin->on_restart();
                else if (do_flip());
                else shift_weights(), m_plugin->on_rescale();
                //verbose_stream() << "steps: " << steps << " min_sz: " << m_min_sz << " unsat: " << m_unsat.size() << "\n";
                ++steps;
            }
        }
        catch (z3_exception& ex) {
            IF_VERBOSE(0, verbose_stream() << "Exception: " << ex.what() << "\n");
            throw;
        }
    }

    void ddfw::log() {
        double sec = m_stopwatch.get_current_seconds();        
        double kflips_per_sec = sec > 0 ? (m_flips - m_last_flips) / (1000.0 * sec) : 0.0;
        if (m_logs++ % 30 == 0) {
            IF_VERBOSE(2, verbose_stream() << "(sat.ddfw :unsat :models :kflips/sec   :flips :restarts   :reinits  :unsat_vars  :shifts";
                       verbose_stream() << ")\n");
        }
        IF_VERBOSE(2, verbose_stream() << "(sat.ddfw " 
                   << std::setw(07) << m_min_sz 
                   << std::setw(07) << m_models.size()
                   << std::setw(11) << std::fixed << std::setprecision(4) << kflips_per_sec
                   << std::setw(10) << m_flips 
                   << std::setw(10) << m_restart_count
                   << std::setw(11) << m_reinit_count
                   << std::setw(13) << m_unsat_vars.size()
                   << std::setw(9) << m_shifts;
                   verbose_stream() << ")\n");
        m_stopwatch.start();
        m_last_flips = m_flips;
    }

    sat::bool_var ddfw::external_flip() {
        flet<bool> _in_external_flip(m_in_external_flip, true);
        double reward = 0;
        bool_var v = pick_var(reward);
        if (apply_flip(v, reward))
            return v;
        shift_weights();
        return sat::null_bool_var;
    }

    bool ddfw::do_flip() {
        double reward = 0;
        bool_var v = pick_var(reward);
        //verbose_stream() << "flip " << v << " " << reward << "\n";
        return apply_flip(v, reward);
    }

    bool ddfw::apply_flip(bool_var v, double reward) {
        if (v == null_bool_var) 
            return false;
        
        if (reward > 0 || (reward == 0 && m_rand(100) <= m_config.m_use_reward_zero_pct)) {
            flip(v);
            if (m_unsat.size() <= m_min_sz)
                save_best_values();
            return true;
        }
        return false;
    }

    bool_var ddfw::pick_var(double& r) {
        double sum_pos = 0;
        unsigned n = 1;
        bool_var v0 = null_bool_var;
        for (bool_var v : m_unsat_vars) {
            r = reward(v);
            if (m_in_external_flip && m_plugin->is_external(v))
                ;
            else if (r > 0.0)    
                sum_pos += score(r);            
            else if (r == 0.0 && sum_pos == 0 && (m_rand() % (n++)) == 0) 
                v0 = v;            
        }
        if (sum_pos > 0) {
            double lim_pos = ((double) m_rand() / (1.0 + m_rand.max_value())) * sum_pos;                
            for (bool_var v : m_unsat_vars) {
                r = reward(v);
                if (m_in_external_flip && m_plugin->is_external(v))
                    continue;
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
        if (m_in_external_flip)
            return null_bool_var;
        return m_unsat_vars.elem_at(m_rand(m_unsat_vars.size()));
    }

    void ddfw::add(unsigned n, literal const* c) {    
        unsigned idx = m_clauses.size();
        m_clauses.push_back(clause_info(n, c, m_config.m_init_clause_weight));
        if (n > 2)
            ++m_num_non_binary_clauses;
        for (literal lit : m_clauses.back().m_clause) {
            m_use_list.reserve(2*(lit.var()+1));
            m_vars.reserve(lit.var()+1);
            m_use_list[lit.index()].push_back(idx);
        }
    }

    sat::bool_var ddfw::add_var() {
        auto v = m_vars.size();
        m_vars.reserve(v + 1);
        return v;
    }

    void ddfw::reserve_vars(unsigned n) {
        m_vars.reserve(n);
    }


    /**
     * Remove the last clause that was added
     */
    void ddfw::del() {
        auto& info = m_clauses.back();
        for (literal lit : info.m_clause)
            m_use_list[lit.index()].pop_back();
        m_clauses.pop_back();
        if (m_unsat.contains(m_clauses.size()))
            m_unsat.remove(m_clauses.size());
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
        if (sz == 0 && m_initialized) {            
            m_stopwatch.start();
            return;
        }
        m_assumptions.reset();
        m_assumptions.append(sz, assumptions);
        add_assumptions();
        for (unsigned v = 0; v < num_vars(); ++v) {
            value(v) = (m_rand() % 2) == 0; // m_use_list[lit.index()].size() >= m_use_list[nlit.index()].size();
        }

        if (!flatten_use_list())
            init_clause_data();

        m_reinit_count = 0;
        m_reinit_next = m_config.m_reinit_base;

        m_restart_count = 0;
        m_restart_next = m_config.m_restart_base;

        m_min_sz = m_clauses.size();
        m_flips = 0;
        m_last_flips = 0;
        m_shifts = 0;
        m_stopwatch.start();
        if (sz == 0)        
            m_initialized = true;
    }

    void ddfw::reinit() {
        add_assumptions();
        flatten_use_list();
    }

    bool ddfw::flatten_use_list() {
        if (num_vars() == m_use_list_vars && m_clauses.size() == m_use_list_clauses)
            return false;
        m_use_list_vars = num_vars();
        m_use_list_clauses = m_clauses.size();
        m_use_list_index.reset();
        m_flat_use_list.reset();
        m_use_list.reserve(2 * num_vars());
        for (auto const& ul : m_use_list) {
            m_use_list_index.push_back(m_flat_use_list.size());
            m_flat_use_list.append(ul);
        }
        m_use_list_index.push_back(m_flat_use_list.size());
        init_clause_data();
        SASSERT(2 * num_vars() + 1 == m_use_list_index.size());
        return true;
    }

    void ddfw::external_flip(bool_var v) {
        flet<bool> _external_flip(m_in_external_flip, true);
        flip(v);
    }

    void ddfw::flip(bool_var v) {
        ++m_flips;
        m_limit.inc();
        literal lit = literal(v, !value(v));
        literal nlit = ~lit;
        SASSERT(is_true(lit));
        for (unsigned cls_idx : use_list(lit)) {
            clause_info& ci = m_clauses[cls_idx];            
            ci.del(lit);
            double w = ci.m_weight;
            // cls becomes false: flip any variable in clause to receive reward w
            switch (ci.m_num_trues) {
            case 0: {
#if 0
                if (ci.m_clause.size() == 1)
                    verbose_stream() << "flipping unit clause " << ci << "\n";
#endif
                m_unsat.insert_fresh(cls_idx);
                auto const& c = get_clause(cls_idx);
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
        for (unsigned cls_idx : use_list(nlit)) {
            clause_info& ci = m_clauses[cls_idx];             
            double w = ci.m_weight;
            // the clause used to have a single true (pivot) literal, now it has two.
            // Then the previous pivot is no longer penalized for flipping.
            switch (ci.m_num_trues) {
            case 0: {
                m_unsat.remove(cls_idx);   
                auto const& c = get_clause(cls_idx);
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
            m_vars[v].m_reward = 0;
        }        
        m_unsat_vars.reset();
        m_num_external_in_unsat_vars = 0;
        m_unsat.reset();
        unsigned sz = m_clauses.size();
        for (unsigned i = 0; i < sz; ++i) {
            auto& ci = m_clauses[i];
            auto const& c = get_clause(i);
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
                m_unsat.insert_fresh(i);
                break;
            case 1:
                dec_reward(to_literal(ci.m_trues), ci.m_weight);
                break;
            default:
                break;
            }
        }
        if (m_unsat.size() < m_min_sz)
            save_best_values();
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

    void ddfw::save_priorities() {
        m_probs.reset();
        for (unsigned v = 0; v < num_vars(); ++v) 
            m_probs.push_back(-m_vars[v].m_reward_avg);         
    }

    void ddfw::save_model() {
        m_model.reserve(num_vars());
        for (unsigned i = 0; i < num_vars(); ++i) 
            m_model[i] = to_lbool(value(i));
        save_priorities();
        if (m_plugin && !m_in_external_flip && m_restart_count == 0 && m_model_save_count++ % 10 == 0)
            m_plugin->on_restart(); // import values if there are any updated ones.
        if (m_plugin && !m_in_external_flip)
            m_last_result = m_plugin->on_save_model();
    }

    void ddfw::save_best_values() {
        if (m_save_best_values)
            return;
        if (m_plugin && !m_unsat.empty())
            return;
        flet<bool> _save_best_values(m_save_best_values, true);

        bool do_save_model = ((m_unsat.size() < m_min_sz || m_unsat.empty()) &&
            ((m_unsat.size() < 50 || m_min_sz * 10 > m_unsat.size() * 11)));

        if (do_save_model)
            save_model();
            
        if (m_unsat.size() < m_min_sz) {
            m_models.reset();
            m_min_sz = m_unsat.size();
        }
        
        unsigned h = value_hash();
        unsigned occs = 0;
        bool contains = m_models.find(h, occs);
        if (!contains) {
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
        auto const& c = ci.m_clause;
        double max_weight = m_init_weight;
        unsigned n = 1;
        for (literal lit : c) {
            for (unsigned cn_idx : use_list(lit)) {
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
        for (unsigned i = 0; i < num_clauses; ++i) {
            unsigned idx = (m_rand() * m_rand()) % num_clauses;
            auto & cn = m_clauses[idx];
            if (cn.is_true() && cn.m_weight >= m_init_weight) 
                return idx;
        }
        unsigned n = 0, idx = UINT_MAX;
        for (unsigned i = 0; i < num_clauses; ++i) {
            auto& cn = m_clauses[i];
            if (cn.is_true() && cn.m_weight >= m_init_weight && (m_rand() % (++n)) == 0)
                idx = i;            
        }
        return idx;
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
        bool shifted = false;
        flatten_use_list();
        for (unsigned to_idx : m_unsat) {
            SASSERT(!m_clauses[to_idx].is_true());
            unsigned from_idx = select_max_same_sign(to_idx);
            if (from_idx == UINT_MAX || disregard_neighbor())
                from_idx = select_random_true_clause();
            if (from_idx == UINT_MAX)
                continue;
            shifted = true;
            auto & cn = m_clauses[from_idx];
            SASSERT(cn.is_true());
            double w = calculate_transfer_weight(cn.m_weight);
            transfer_weight(from_idx, to_idx, w);
        }
        //verbose_stream() << m_shifts << " " << m_flips << " " << shifted << "\n";
        if (!shifted && m_restart_next > m_flips)
            m_restart_next =  m_flips + (m_restart_next - m_flips) / 2;
        // DEBUG_CODE(invariant(););
    }

    // apply unit propagation.
    void ddfw::simplify() {
        verbose_stream() << "simplify\n";
        sat::literal_vector units;
        uint_set unit_set;
        for (unsigned i = 0; i < m_clauses.size(); ++i) {
            auto& ci = m_clauses[i];
            if (ci.m_clause.size() != 1)
                continue;
            auto lit = ci.m_clause[0];
            units.push_back(lit);
            unit_set.insert(lit.index());
            m_use_list[lit.index()].reset();
            m_use_list[lit.index()].push_back(i);
        }
        auto is_unit = [&](sat::literal lit) {
            return unit_set.contains(lit.index());
        };

        sat::literal_vector new_clause;
        for (unsigned i = 0; i < units.size(); ++i) {
            auto lit = units[i];
            for (auto cidx : m_use_list[(~lit).index()]) {
                auto& ci = m_clauses[cidx];
                if (ci.m_clause.size() == 1)
                    continue;
                new_clause.reset();
                for (auto l : ci) {
                    if (!is_unit(~l))
                        new_clause.push_back(l);
                }
                if (new_clause.size() == 1) {
                    verbose_stream() << "new unit " << lit << " " << ci << " -> " << new_clause << "\n";
                }
                m_clauses[cidx] = sat::clause_info(new_clause.size(), new_clause.data(), m_config.m_init_clause_weight);
                if (new_clause.size() == 1) {
                    units.push_back(new_clause[0]);
                    unit_set.insert(new_clause[0].index());
                }
            }
        }
        for (auto unit : units) 
            m_use_list[(~unit).index()].reset();        
    }

    bool ddfw::try_rotate(bool_var v, bool_var_set& rotated, unsigned& budget) {
        if (m_rotate_tabu.contains(v))
            return false;
        if (budget == 0)
            return false;
        --budget;
        rotated.insert(v);
        m_rotate_tabu.insert(v);
        flip(v);
        switch (m_unsat.size()) {
        case 0:
            m_rotate_tabu.reset();
            m_new_tabu_vars.reset();
            return true;
        case 1: 
            for (unsigned cl : m_unsat) {
                unsigned sz = m_new_tabu_vars.size();
                for (literal lit : get_clause(cl)) {
                    if (m_rotate_tabu.contains(lit.var()))
                        continue;
                    if (try_rotate(lit.var(), rotated, budget))
                        return true;
                    m_rotate_tabu.insert(lit.var());
                    m_new_tabu_vars.push_back(lit.var());
                }
                while (m_new_tabu_vars.size() > sz)
                    m_rotate_tabu.remove(m_new_tabu_vars.back()), m_new_tabu_vars.pop_back();
            }
            break;
        default:
            break;
        }
        rotated.remove(v); 
        m_rotate_tabu.remove(v);
        flip(v);
        return false;
    }

    std::ostream& ddfw::display(std::ostream& out) const {
        unsigned num_cls = m_clauses.size();
        for (unsigned i = 0; i < num_cls; ++i) {
            out << get_clause(i) << " nt: ";
            auto const& ci = m_clauses[i];
            out << ci.m_num_trues << " w: " << ci.m_weight << "\n";
        }
        for (unsigned v = 0; v < num_vars(); ++v) 
            out << (is_true(literal(v, false)) ? "" : "-") << v << " rw: " << reward(v) << "\n";        
        out << "unsat vars: ";
        for (bool_var v : m_unsat_vars) 
            out << v << " ";        
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

    void ddfw::collect_statistics(statistics& st) const {
        st.update("sls-ddfw-flips", (double)m_flips);
        st.update("sls-ddfw-restarts", m_restart_count);
        st.update("sls-ddfw-reinits", m_reinit_count);
        st.update("sls-ddfw-shifts", (double)m_shifts);
    }
    
    void ddfw::reset_statistics() {
        m_flips = 0;
        m_restart_count = 0;
        m_reinit_count = 0;
        m_shifts = 0;
    }

}

