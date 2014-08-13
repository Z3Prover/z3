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
        m_max_tries = 10000;
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
        for (i = 0; !m_false.empty() && i < m_max_tries; ++i) {
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
        // IF_VERBOSE(0, verbose_stream() << lit << " ";);
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

};

