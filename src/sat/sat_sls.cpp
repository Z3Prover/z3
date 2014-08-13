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
    }

    sls::~sls() {
        for (unsigned i = 0; i < m_bin_clauses.size(); ++i) {
            m_alloc.del_clause(m_bin_clauses[i]);
        }
    }

    lbool sls::operator()(unsigned sz, literal const* tabu) {
        init(sz, tabu);
        
        for (unsigned i = 0; i < m_max_tries; ++i) {
            flip();
            if (m_false.empty()) {
                SASSERT(s.check_model(m_model));
                return l_true;
            }
        }
        return l_undef;
    }

    void sls::init(unsigned sz, literal const* tabu) {
        init_clauses();
        init_model(sz, tabu);
        init_use();            
    }

    void sls::init_clauses() {
        for (unsigned i = 0; i < m_bin_clauses.size(); ++i) {
            m_alloc.del_clause(m_bin_clauses[i]);
        }
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
            m_clauses.push_back(m_alloc.mk_clause(2, lits, false));
        }
    }

    void sls::init_model(unsigned sz, literal const* tabu) {
        m_num_true.reset();
        m_model.reset();
        m_model.append(s.get_model());
        m_tabu.reset();
        m_tabu.resize(s.num_vars(), false);
        for (unsigned i = 0; i < sz; ++i) {
            m_model[tabu[i].var()] = tabu[i].sign()?l_false:l_true;
        }

        sz = m_clauses.size();
        for (unsigned i = 0; i < sz; ++i) {
            clause const& c = *m_clauses[i];
            unsigned n = 0;
            unsigned csz = c.size();
            for (unsigned j = 0; j < csz; ++j) {
                if (value_at(c[j], m_model) == l_true) {
                    ++n;
                }
            }
            m_num_true.push_back(n);
            if (n == 0) {
                m_false.insert(i);
            }
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
        if (min_break == 0 || (m_min_vars.empty() && m_rand(100) >= m_prob_choose_min_var)) {
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
        if (!pick_flip(lit)) return;
        SASSERT(value_at(lit, m_model) == l_false);
        m_model[lit.var()] = lit.sign()?l_true:l_false;
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

