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

    }

    sls::~sls() {
        
    }

#if 0
    bool_var sls::pick_flip() {
        unsigned clause_idx = m_false.choose(m_rand);
        clause const& c = m_clauses[clause_idx];
        unsigned result =  UINT_MAX;
        m_min_vars.reset();
        for (unsigned i = 0; i < c.size(); ++i) {
            
        }
    }

    void sls::flip(bool_var v) {

    }

    bool sls::local_search() {
        for (unsigned i = 0; !m_false.empty() && i < m_max_flips; ++i) {
            flip(pick_flip());
        }        
        return m_false.empty();
    }

#endif

    lbool sls::operator()() {
#if 0
        for (unsigned i = 0; i < m_max_tries; ++i) {
            if (local_search()) {
                return l_true;
            }
        }
#endif
        return l_undef;
    }

};

