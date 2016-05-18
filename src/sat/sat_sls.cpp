/*++
Copyright (c) 2014 Microsoft Corporation

Module Name:

    sat_sls.cpp

Abstract:
   
    SLS for clauses in SAT solver

Author:

    Nikolaj Bjorner (nbjorner) 2014-12-8

Notes:

--*/

#include "sat_sls.h"
#include "sat_solver.h"

namespace sat {

    bool index_set::contains(unsigned idx) const {
        return 
            (idx < m_index.size()) && 
            (m_index[idx] < m_elems.size()) && 
            (m_elems[m_index[idx]] == idx);
    }
        
    void index_set::insert(unsigned idx) {
        m_index.reserve(idx+1);
        if (!contains(idx)) {
            m_index[idx] = m_elems.size();
            m_elems.push_back(idx);
        }
    }
        
    void index_set::remove(unsigned idx) {
        if (!contains(idx)) return;
        unsigned pos = m_index[idx];
        m_elems[pos] = m_elems.back();
        m_index[m_elems[pos]] = pos;
        m_elems.pop_back();
    }
        
    unsigned index_set::choose(random_gen& rnd) const {
        SASSERT(!empty());
        return m_elems[rnd(num_elems())];
    }

    sls::sls(solver& s): s(s) {
        m_prob_choose_min_var = 43;
        m_clause_generation = 0;
    }

    sls::~sls() {
        for (unsigned i = 0; i < m_bin_clauses.size(); ++i) {
            m_alloc.del_clause(m_bin_clauses[i]);
        }
    }

    lbool sls::operator()(unsigned sz, literal const* tabu, bool reuse_model) {
        init(sz, tabu, reuse_model);
        unsigned i;
        for (i = 0; !m_false.empty() && !s.canceled() && i < m_max_tries; ++i) {
            flip();
        }
        IF_VERBOSE(2, verbose_stream() << "tries " << i << "\n";);
        if (m_false.empty()) {
            SASSERT(s.check_model(m_model));
            return l_true;
        }
        return l_undef;
    }

    void sls::init(unsigned sz, literal const* tabu, bool reuse_model) {
        bool same_generation = (m_clause_generation == s.m_stats.m_non_learned_generation);
        if (!same_generation) {
            init_clauses();
            init_use();          
            IF_VERBOSE(0, verbose_stream() << s.m_stats.m_non_learned_generation << " " << m_clause_generation << "\n";);  
        }
        if (!reuse_model) {
            init_model();
        }
        init_tabu(sz, tabu);
        m_clause_generation = s.m_stats.m_non_learned_generation;

        m_max_tries = 10*(s.num_vars() + m_clauses.size());

    }

    void sls::init_clauses() {
        for (unsigned i = 0; i < m_bin_clauses.size(); ++i) {
            m_alloc.del_clause(m_bin_clauses[i]);
        }
        m_bin_clauses.reset();
        m_clauses.reset();
        clause * const * it = s.begin_clauses();
        clause * const * end = s.end_clauses();
        for (; it != end; ++it) {
            m_clauses.push_back(*it);
        }
        svector<solver::bin_clause> bincs;
        s.collect_bin_clauses(bincs, false);
        literal lits[2];
        for (unsigned i = 0; i < bincs.size(); ++i) {
            lits[0] = bincs[i].first;
            lits[1] = bincs[i].second;
            clause* cl = m_alloc.mk_clause(2, lits, false);
            m_clauses.push_back(cl);
            m_bin_clauses.push_back(cl);
        }
    }

    void sls::init_model() {
        m_num_true.reset();
        m_model.reset();
        m_model.append(s.get_model());
        unsigned sz = m_clauses.size();
        for (unsigned i = 0; i < sz; ++i) {
            clause const& c = *m_clauses[i];
            unsigned n = 0;
            unsigned csz = c.size();
            for (unsigned j = 0; j < csz; ++j) {
                lbool val = value_at(c[j], m_model);
                switch (val) {
                case l_true:
                    ++n;
                    break;
                case l_undef:
                    ++n;
                    m_model[c[j].var()] = c[j].sign()?l_false:l_true;
                    SASSERT(value_at(c[j], m_model) == l_true);
                    break;
                default:
                    break;                
                }
            }
            m_num_true.push_back(n);
            if (n == 0) {
                m_false.insert(i);
            }
        } 
    }

    void sls::init_tabu(unsigned sz, literal const* tabu) {        
        // our main use is where m_model satisfies all the hard constraints.
        // SASSERT(s.check_model(m_model));
        // SASSERT(m_false.empty());
        // ASSERT: m_num_true is correct count.       
        m_tabu.reset();
        m_tabu.resize(s.num_vars(), false);
        for (unsigned i = 0; i < sz; ++i) {
            literal lit = tabu[i];
            if (s.m_level[lit.var()] == 0) continue;
            if (value_at(lit, m_model) == l_false) {
                flip(lit);                
            }
            m_tabu[lit.var()] = true;
        }
        for (unsigned i = 0; i < s.m_trail.size(); ++i) {
            literal lit = s.m_trail[i];
            if (s.m_level[lit.var()] > 0) break;
            if (value_at(lit, m_model) != l_true) {
                flip(lit);
            }           
            m_tabu[lit.var()] = true;
        }    
    }

    void sls::init_use() {
        m_use_list.reset();
        m_use_list.resize(s.num_vars()*2);
        unsigned sz = m_clauses.size();
        for (unsigned i = 0; i < sz; ++i) {
            clause const& c = *m_clauses[i];
            unsigned csz = c.size();
            for (unsigned j = 0; j < csz; ++j) {
                m_use_list[c[j].index()].push_back(i);
            }
        }
        DEBUG_CODE(check_use_list(););
    }

    unsigned_vector const& sls::get_use(literal lit) {
        SASSERT(lit.index() < m_use_list.size());
        return m_use_list[lit.index()];        
    }

    unsigned sls::get_break_count(literal lit, unsigned min_break) {
        SASSERT(value_at(lit, m_model) == l_false);
        unsigned result = 0;
        unsigned_vector const& uses = get_use(~lit);
        unsigned sz = uses.size();
        for (unsigned i = 0; i < sz; ++i) {
            if (m_num_true[uses[i]] == 1) {
                ++result;
                if (result > min_break) return result;
            }
        }
        return result;
    }

    bool sls::pick_flip(literal& lit) {
        unsigned clause_idx = m_false.choose(m_rand);
        clause const& c = *m_clauses[clause_idx];
        SASSERT(!c.satisfied_by(m_model));
        unsigned min_break =  UINT_MAX;
        unsigned sz = c.size();
        m_min_vars.reset();
        for (unsigned i = 0; i < sz; ++i) {
            lit = c[i];
            if (m_tabu[lit.var()]) continue;
            unsigned break_count = get_break_count(lit, min_break);
            if (break_count < min_break) {
                min_break = break_count;
                m_min_vars.reset();
                m_min_vars.push_back(lit);
            }
            else if (break_count == min_break) {
                m_min_vars.push_back(lit);
            }
        }
        if (min_break == 0 || (!m_min_vars.empty() && m_rand(100) >= m_prob_choose_min_var)) {
            lit = m_min_vars[m_rand(m_min_vars.size())];
            return true;
        }
        else if (min_break == UINT_MAX) {
            return false;
        }
        else {
            lit = c[m_rand(c.size())];
            return !m_tabu[lit.var()];
        }
    }

    void sls::flip() {
        literal lit;
        if (pick_flip(lit)) {
            flip(lit);
        }
    }

    void sls::flip(literal lit) {
        //IF_VERBOSE(0, verbose_stream() << lit << " ";);
        SASSERT(value_at(lit, m_model) == l_false);
        SASSERT(!m_tabu[lit.var()]);
        m_model[lit.var()] = lit.sign()?l_false:l_true;
        SASSERT(value_at(lit, m_model) == l_true);
        unsigned_vector const& use1 = get_use(lit);
        unsigned sz = use1.size();
        for (unsigned i = 0; i < sz; ++i) {
            unsigned cl = use1[i]; 
            m_num_true[cl]++;
            SASSERT(m_num_true[cl] <= m_clauses[cl]->size());
            if (m_num_true[cl] == 1) m_false.remove(cl);
        }
        unsigned_vector const& use2 = get_use(~lit);
        sz = use2.size();
        for (unsigned i = 0; i < sz; ++i) {
            unsigned cl = use2[i]; 
            SASSERT(m_num_true[cl] > 0);
            m_num_true[cl]--;
            if (m_num_true[cl] == 0) m_false.insert(cl);
        }        
    }

    void sls::check_invariant() {
        DEBUG_CODE(
            for (unsigned i = 0; i < m_clauses.size(); ++i) {
                clause const& c = *m_clauses[i];
                bool is_sat = c.satisfied_by(m_model);
                SASSERT(is_sat != m_false.contains(i));
                SASSERT(is_sat == (m_num_true[i] > 0));
            });
    }

    void sls::check_use_list() {
        DEBUG_CODE(
            for (unsigned i = 0; i < m_clauses.size(); ++i) {
                clause const& c = *m_clauses[i];
                for (unsigned j = 0; j < c.size(); ++j) {
                    unsigned idx = c[j].index();
                    SASSERT(m_use_list[idx].contains(i));
                }
            }

            for (unsigned i = 0; i < m_use_list.size(); ++i) {
                literal lit = to_literal(i);
                for (unsigned j = 0; j < m_use_list[i].size(); ++j) {
                    clause const& c = *m_clauses[m_use_list[i][j]];
                    bool found = false;
                    for (unsigned k = 0; !found && k < c.size(); ++k) {
                        found = c[k] == lit;
                    }
                    SASSERT(found);
                }
            });
    }

    void sls::display(std::ostream& out) const {
        out << "Model\n";
        for (bool_var v = 0; v < m_model.size(); ++v) {
            out << v << ": " << m_model[v] << "\n";
        }
        out << "Clauses\n";
        unsigned sz = m_false.num_elems();
        for (unsigned i = 0; i < sz; ++i) {
            out << *m_clauses[m_false[i]] << "\n";
        }
        for (unsigned i = 0; i < m_clauses.size(); ++i) {
            if (m_false.contains(i)) continue;
            clause const& c = *m_clauses[i];
            out << c << " " << m_num_true[i] << "\n";
        }
        bool has_tabu = false;
        for (unsigned i = 0; !has_tabu && i < m_tabu.size(); ++i) {
            has_tabu = m_tabu[i];
        }
        if (has_tabu) {
            out << "Tabu: ";
            for (unsigned i = 0; i < m_tabu.size(); ++i) {
                if (m_tabu[i]) {
                    literal lit(i, false);
                    if (value_at(lit, m_model) == l_false) lit.neg();
                    out << lit << " ";
                }
            }
            out << "\n";
        }
    }


    wsls::wsls(solver& s):
        sls(s)
    {
        m_smoothing_probability = 1; // 1/1000
    }

    wsls::~wsls() {}

    void wsls::set_soft(unsigned sz, literal const* lits, double const* weights) {
        m_soft.reset();
        m_weights.reset();
        m_soft.append(sz, lits);
        m_weights.append(sz, weights);
    }
        
    void wsls::opt(unsigned sz, literal const* tabu, bool reuse_model) {
        init(sz, tabu, reuse_model);

        //
        // Initialize m_clause_weights, m_hscore, m_sscore.
        //
        m_best_value = m_false.empty()?evaluate_model(m_model):-1.0;        
        m_best_model.reset();
        m_clause_weights.reset();
        m_hscore.reset();
        m_sscore.reset();
        m_H.reset();
        m_S.reset();
        m_best_model.append(s.get_model());
        m_clause_weights.resize(m_clauses.size(), 1);
        m_sscore.resize(s.num_vars(), 0.0);
        m_hscore.resize(s.num_vars(), 0);
        for (unsigned i = 0; i < m_soft.size(); ++i) {
            literal lit = m_soft[i];
            m_sscore[lit.var()] = m_weights[i];
            if (value_at(lit, m_model) == l_true) {
                m_sscore[lit.var()] = -m_sscore[lit.var()];
            }
        }
        for (bool_var i = 0; i < s.num_vars(); ++i) {
            m_hscore[i] = compute_hscore(i);
            refresh_scores(i);
        }
        DEBUG_CODE(check_invariant(););
        unsigned i = 0;
        for (; !s.canceled() && m_best_value > 0 && i < m_max_tries; ++i) {
            wflip();
            if (m_false.empty()) {
                double val = evaluate_model(m_model);
                if (val < m_best_value || m_best_value < 0.0) {
                    m_best_value = val;
                    m_best_model.reset();
                    m_best_model.append(m_model);
                    s.set_model(m_best_model);
                    IF_VERBOSE(1, verbose_stream() << "new value: " << val << " @ " << i << "\n";);
                    if (i*2 > m_max_tries) {
                        m_max_tries *= 2;
                    }
                }
            }
        }
        TRACE("sat", display(tout););
        IF_VERBOSE(0, verbose_stream() << "tries " << i << "\n";);
    }

    void wsls::wflip() {
        literal lit;
        if (pick_wflip(lit)) {
            // IF_VERBOSE(0, verbose_stream() << lit << " ";);
            wflip(lit);
        }
    }

    bool wsls::pick_wflip(literal & lit) {
        unsigned idx;
        if (!m_H.empty()) {
            idx = m_H.choose(m_rand);
            lit = literal(idx, false);
            if (value_at(lit, m_model) == l_true) lit.neg();            
            SASSERT(value_at(lit, m_model) == l_false); 
            TRACE("sat", tout << "flip H(" << m_H.num_elems() << ") " << lit << "\n";);
        }
        else if (!m_S.empty()) {
            double score = 0.0;
            m_min_vars.reset();
            for (unsigned i = 0; i < m_S.num_elems(); ++i) {
                unsigned v = m_S[i];
                SASSERT(m_sscore[v] > 0.0);
                if (m_sscore[v] > score) {
                    m_min_vars.reset();
                    m_min_vars.push_back(literal(v, false));
                    score = m_sscore[v];
                }
                else if (m_sscore[v] == score) {
                    m_min_vars.push_back(literal(v, false));
                }
            }
            lit = m_min_vars[m_rand(m_min_vars.size())]; // pick with largest sscore.
            SASSERT(value_at(lit, m_model) == l_false);
            TRACE("sat", tout << "flip S(" << m_min_vars.size() << "," << score << ") " << lit << "\n";);
        }
        else {
            update_hard_weights();
            if (!m_false.empty()) {
                unsigned cls_idx = m_false.choose(m_rand);
                clause const& c = *m_clauses[cls_idx]; 
                lit = c[m_rand(c.size())];
                TRACE("sat", tout << "flip hard(" << m_false.num_elems() << "," << c.size() << ") " << lit << "\n";);
            }
            else {
                m_min_vars.reset();
                for (unsigned i = 0; i < m_soft.size(); ++i) {
                    lit = m_soft[i];
                    if (value_at(lit, m_model) == l_false) {
                        m_min_vars.push_back(lit);
                    }
                }
                if (m_min_vars.empty()) {
                    SASSERT(m_best_value == 0.0);
                    UNREACHABLE(); // we should have exited the main loop before.
                    return false; 
                }
                else {
                    lit = m_min_vars[m_rand(m_min_vars.size())];
                }
                TRACE("sat", tout << "flip soft(" << m_min_vars.size() << ", " << m_sscore[lit.var()] << ") " << lit << "\n";);

            }
            SASSERT(value_at(lit, m_model) == l_false);
        }
        return !m_tabu[lit.var()];
    }

    void wsls::wflip(literal lit) {
        flip(lit);
        unsigned v = lit.var();
        m_sscore[v] = -m_sscore[v];
        m_hscore[v] = compute_hscore(v);
        refresh_scores(v);
        recompute_hscores(lit);
    }

    void wsls::update_hard_weights() {
        unsigned csz = m_clauses.size();
        if (m_smoothing_probability >= m_rand(1000)) {
            for (unsigned i = 0; i < csz; ++i) {
                if (m_clause_weights[i] > 1 && !m_false.contains(i)) {
                    --m_clause_weights[i];
                    if (m_num_true[i] == 1) {
                        clause const& c = *m_clauses[i];
                        unsigned sz = c.size();
                        for (unsigned j = 0; j < sz; ++j) {
                            if (value_at(c[j], m_model) == l_true) {
                                ++m_hscore[c[j].var()];
                                refresh_scores(c[j].var());
                                break;
                            }
                        }                        
                    }
                }
            }
        }
        else {
            for (unsigned i = 0; i < csz; ++i) {
                if (m_false.contains(i)) {
                    ++m_clause_weights[i];
                    clause const& c = *m_clauses[i];
                    unsigned sz = c.size();
                    for (unsigned j = 0; j < sz; ++j) {
                        ++m_hscore[c[j].var()];
                        refresh_scores(c[j].var());
                    }
                }
            }
        }
        DEBUG_CODE(check_invariant(););
    }

    double wsls::evaluate_model(model& mdl) {
        SASSERT(m_false.empty());
        double result = 0.0;
        for (unsigned i = 0; i < m_soft.size(); ++i) {
            literal lit = m_soft[i];
            if (value_at(lit, mdl) != l_true) {
                result += m_weights[i];
            }
        }
        return result;
    }

    int wsls::compute_hscore(bool_var v) {
        literal lit(v, false);
        if (value_at(lit, m_model) == l_false) {
            lit.neg();
        }
        SASSERT(value_at(lit, m_model) == l_true);
        int hs = 0;
        unsigned_vector const& use1 = get_use(~lit);
        unsigned sz = use1.size();
        for (unsigned i = 0; i < sz; ++i) {
            unsigned cl = use1[i]; 
            if (m_num_true[cl] == 0) {
                SASSERT(m_false.contains(cl));
                hs += m_clause_weights[cl];
            } 
            else {
                SASSERT(!m_false.contains(cl));
            }
        }
        unsigned_vector const& use2 = get_use(lit);
        sz = use2.size();
        for (unsigned i = 0; i < sz; ++i) {
            unsigned cl = use2[i]; 
            if (m_num_true[cl] == 1) {
                SASSERT(!m_false.contains(cl));
                hs -= m_clause_weights[cl];
            }
        }
        return hs;
    }

    void wsls::recompute_hscores(literal lit) {
        SASSERT(value_at(lit, m_model) == l_true);
        TRACE("sat", tout << lit.var() << " := " << m_hscore[lit.var()] << "\n";);
        unsigned_vector const& use1 = get_use(lit);
        unsigned sz = use1.size();
        for (unsigned i = 0; i < sz; ++i) {
            unsigned cl = use1[i];
            TRACE("sat", tout << *m_clauses[cl] << " " << m_num_true[cl] << "\n";);
            SASSERT(m_num_true[cl] > 0);
            if (m_num_true[cl] == 1) {     
                // num_true 0 -> 1
                // other literals don't have upside any more.
                // subtract one from all other literals
                adjust_all_values(lit, cl, -static_cast<int>(m_clause_weights[cl]));
            }
            else if (m_num_true[cl] == 2) {
                // num_true 1 -> 2, previous critical literal is no longer critical
                adjust_pivot_value(lit, cl, +m_clause_weights[cl]);
            }
        }
        unsigned_vector const& use2 = get_use(~lit);
        sz = use2.size();
        for (unsigned i = 0; i < sz; ++i) {
            unsigned cl = use2[i]; 
            TRACE("sat", tout << *m_clauses[cl] << " " << m_num_true[cl] << "\n";);
            if (m_num_true[cl] == 0) {
                // num_true 1 -> 0
                // all variables became critical.
                adjust_all_values(~lit, cl, +m_clause_weights[cl]);
            }
            else if (m_num_true[cl] == 1) {
                adjust_pivot_value(~lit, cl, -static_cast<int>(m_clause_weights[cl]));
            }
            // else n+1 -> n >= 2
        }
    }

    void wsls::adjust_all_values(literal lit, unsigned cl, int delta) {
        clause const& c = *m_clauses[cl];
        unsigned sz = c.size();
        TRACE("sat", tout << lit << " " << c << " delta: " << delta << " nt: " << m_num_true[cl] << "\n";);
        for (unsigned i = 0; i < sz; ++i) {
            literal lit2 = c[i];
            if (lit2 != lit) {
                TRACE("sat", tout << lit2.var() << " := " << m_hscore[lit2.var()] << "\n";);
                m_hscore[lit2.var()] += delta;
                TRACE("sat", tout << lit2.var() << " := " << m_hscore[lit2.var()] << "\n";);
                refresh_scores(lit2.var());
            }
        }
    }

    void wsls::adjust_pivot_value(literal lit, unsigned cl, int delta) {
        clause const& c = *m_clauses[cl];
        unsigned csz = c.size();
        for (unsigned j = 0; j < csz; ++j) {
            literal lit2 = c[j];
            if (lit2 != lit && value_at(lit2, m_model) == l_true) {
                TRACE("sat", tout << lit2.var() << " := " << m_hscore[lit2.var()] << "\n";);
                m_hscore[lit2.var()] += delta;
                TRACE("sat", tout << lit2.var() << " := " << m_hscore[lit2.var()] << "\n";);
                refresh_scores(lit2.var());
                break;
            }
        }
    }

    void wsls::refresh_scores(bool_var v) {
        if (m_hscore[v] > 0 && !m_tabu[v] && m_sscore[v] == 0) {
            m_H.insert(v);
        }
        else {
            m_H.remove(v);
        }
        if (m_sscore[v] > 0) {
            if (m_hscore[v] == 0 && !m_tabu[v]) {
                m_S.insert(v);
            }
            else {
                m_S.remove(v);
            }
        }
        else if (m_sscore[v] < 0) {
            m_S.remove(v);
        }
    }

    void wsls::check_invariant() {
        sls::check_invariant();
        // The hscore is the reward for flipping the truth value of variable v.
        // hscore(v) = Sum weight(c) for num_true(c) = 0 and v in c
        //           - Sum weight(c) for num_true(c) = 1 and (v in c, M(v) or !v in c and !M(v)) 
        DEBUG_CODE(
            for (unsigned v = 0; v < s.num_vars(); ++v) {
                int hs = compute_hscore(v);
                CTRACE("sat", hs != m_hscore[v], display(tout << v << " - computed: " << hs << " - assigned: " << m_hscore[v] << "\n"););
                SASSERT(m_hscore[v] == hs);
            }
            
            // The score(v) is the reward on soft clauses for flipping v.
            for (unsigned j = 0; j < m_soft.size(); ++j) {
                unsigned v = m_soft[j].var();
                double ss = (l_true == value_at(m_soft[j], m_model))?(-m_weights[j]):m_weights[j];
                SASSERT(m_sscore[v] == ss);
            }
            
            // m_H are values such that m_hscore > 0 and sscore = 0.
            for (bool_var v = 0; v < m_hscore.size(); ++v) {
                SASSERT((m_hscore[v] > 0 && !m_tabu[v] && m_sscore[v] == 0) == m_H.contains(v));
            }
            
            // m_S are values such that hscore = 0, sscore > 0
            for (bool_var v = 0; v < m_sscore.size(); ++v) {
                SASSERT((m_hscore[v] == 0 && m_sscore[v] > 0 && !m_tabu[v]) == m_S.contains(v));
            });
    }

    void wsls::display(std::ostream& out) const {
        sls::display(out);
        out << "Best model\n";
        for (bool_var v = 0; v < m_best_model.size(); ++v) {
            out << v << ": " << m_best_model[v] << " h: " << m_hscore[v];
            if (m_sscore[v] != 0.0) out << " s: " << m_sscore[v];
            out << "\n";
        }        
    }

};

