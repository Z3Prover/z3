/*++
Copyright (c) 2011 Microsoft Corporation

Module Name:

    sat_asymm_branch.cpp

Abstract:

    SAT solver asymmetric branching

Author:

    Leonardo de Moura (leonardo) 2011-05-30.

Revision History:

--*/
#include "sat/sat_asymm_branch.h"
#include "sat/sat_asymm_branch_params.hpp"
#include "sat/sat_solver.h"
#include "sat/sat_big.h"
#include "util/stopwatch.h"
#include "util/trace.h"

namespace sat {

    asymm_branch::asymm_branch(solver & _s, params_ref const & p):
        s(_s),
        m_params(p),
        m_counter(0) {
        updt_params(p);
        reset_statistics();
        m_calls = 0;
    }

    struct clause_size_lt {
        bool operator()(clause * c1, clause * c2) const { return c1->size() > c2->size(); }
    };

    struct asymm_branch::report {
        asymm_branch & m_asymm_branch;
        stopwatch      m_watch;
        unsigned       m_elim_literals;
        unsigned       m_elim_learned_literals;
        unsigned       m_hidden_tautologies;
        report(asymm_branch & a):
            m_asymm_branch(a),
            m_elim_literals(a.m_elim_literals),
            m_elim_learned_literals(a.m_elim_learned_literals),
            m_hidden_tautologies(a.m_hidden_tautologies) {
            m_watch.start();
        }
        
        ~report() {
            m_watch.stop();
            IF_VERBOSE(SAT_VB_LVL, 
                       verbose_stream() << " (sat-asymm-branch :elim-literals "
                       << (m_asymm_branch.m_elim_literals - m_elim_literals)
                       << " :elim-learned-literals " << (m_asymm_branch.m_elim_learned_literals - m_elim_learned_literals)
                       << " :hidden-tautologies " << (m_asymm_branch.m_hidden_tautologies - m_hidden_tautologies)
                       << " :cost " << m_asymm_branch.m_counter
                       << mem_stat()
                       << " :time " << std::fixed << std::setprecision(2) << m_watch.get_seconds() << ")\n";);
        }
    };

    bool asymm_branch::process(big* big) {
        unsigned elim0 = m_elim_literals;
        unsigned eliml0 = m_elim_learned_literals;
        for (unsigned i = 0; i < m_asymm_branch_rounds; ++i) {
            unsigned elim = m_elim_literals;
            if (big) big->init_big(s, true);
            process(big, s.m_clauses);
            if (big) process(big, s.m_learned);
            s.propagate(false); 
            if (s.m_inconsistent)
                break;
            //std::cout << "elim: " << m_elim_literals - elim << "\n";
            if (m_elim_literals == elim)
                break;
        }
        //std::cout << "elim-literals: " << m_elim_literals - elim0 << "\n";
        //std::cout << "elim-learned-literals: " << m_elim_learned_literals - eliml0 << "\n";
        return m_elim_literals > elim0;
    }


    void asymm_branch::process(big* big, clause_vector& clauses) {
        int64 limit = -m_asymm_branch_limit;
        std::stable_sort(clauses.begin(), clauses.end(), clause_size_lt());
        m_counter -= clauses.size();
        SASSERT(s.m_qhead == s.m_trail.size());
        clause_vector::iterator it  = clauses.begin();
        clause_vector::iterator it2 = it;
        clause_vector::iterator end = clauses.end();
        try {
            for (; it != end; ++it) {
                if (s.inconsistent()) {
                    for (; it != end; ++it, ++it2) {
                        *it2 = *it;
                    }
                    break;
                }
                SASSERT(s.m_qhead == s.m_trail.size());
                if (m_counter < limit || s.inconsistent()) {
                    *it2 = *it;
                    ++it2;
                    continue;
                }
                s.checkpoint();
                clause & c = *(*it);
                if (big ? !process_sampled(*big, c) : !process(c)) {
                    continue; // clause was removed
                }
                *it2 = *it;
                ++it2;
            }
            clauses.set_end(it2);
        }
        catch (solver_exception & ex) {
            // put m_clauses in a consistent state...
            for (; it != end; ++it, ++it2) {
                *it2 = *it;
            }
            clauses.set_end(it2);
            m_counter = -m_counter;
            throw ex;
        }
    }
    
    void asymm_branch::operator()(bool force) {
        ++m_calls;
        if (m_calls <= m_asymm_branch_delay)
            return;
        if (!m_asymm_branch && !m_asymm_branch_all && !m_asymm_branch_sampled)
            return;
        s.propagate(false); // must propagate, since it uses s.push()
        if (s.m_inconsistent)
            return;
        if (!force && m_counter > 0) {
            m_counter /= 100;
            return;
        }
        CASSERT("asymm_branch", s.check_invariant());
        TRACE("asymm_branch_detail", s.display(tout););
        report rpt(*this);
        svector<char> saved_phase(s.m_phase);

        bool change = true;
        unsigned counter = 0;
        while (change && counter < 2) {
            ++counter;
            change = false;
            if (m_asymm_branch_sampled) {
                big big;
                if (process(&big)) change = true;
            }
            if (m_asymm_branch) {
                m_counter  = 0; 
                if (process(nullptr)) change = true;
                m_counter = -m_counter;
            }
        }

        s.m_phase = saved_phase;
        m_asymm_branch_limit *= 2;
        if (m_asymm_branch_limit > UINT_MAX)
            m_asymm_branch_limit = UINT_MAX;

        CASSERT("asymm_branch", s.check_invariant());
    }

    /**
       \brief try asymmetric branching on all literals in clause.        
    */

    bool asymm_branch::process_all(clause & c) {
        scoped_detach scoped_d(s, c);  // clause must not be used for propagation
        unsigned sz = c.size();
        SASSERT(sz > 0);
        unsigned i = 0, new_sz = sz;
        for (i = sz; i-- > 0; ) {
            if (flip_literal_at(c, i, new_sz))
                return cleanup(scoped_d, c, i, new_sz);
        }
        return true;
    }

    struct asymm_branch::compare_left {
        big& s;
        compare_left(big& s): s(s) {}
        bool operator()(literal u, literal v) const {
            return s.get_left(u) < s.get_left(v);
        }
    };

    void asymm_branch::sort(big& big, clause const& c) {
        sort(big, c.begin(), c.end());
    }

    void asymm_branch::sort(big& big, literal const* begin, literal const* end) {
        m_pos.reset(); m_neg.reset();
        for (; begin != end; ++begin) {
            literal l = *begin;
            m_pos.push_back(l);
            m_neg.push_back(~l);
        }
        compare_left cmp(big);
        std::sort(m_pos.begin(), m_pos.end(), cmp);
        std::sort(m_neg.begin(), m_neg.end(), cmp);
    }

    bool asymm_branch::uhte(big& big, clause & c) {
        unsigned pindex = 0, nindex = 0;
        literal lpos = m_pos[pindex++];
        literal lneg = m_neg[nindex++];
        while (true) {
            if (big.get_left(lneg) > big.get_left(lpos)) {
                if (pindex == m_pos.size()) return false;
                lpos = m_pos[pindex++];
            }
            else if (big.get_right(lneg) < big.get_right(lpos) ||
                     (m_pos.size() == 2 && (lpos == ~lneg || big.get_parent(lpos) == lneg))) {
                if (nindex == m_neg.size()) return false;
                lneg = m_neg[nindex++];
            }
            else {
                return true;
            }
        }
        return false;
    }

    void asymm_branch::minimize(big& big, literal_vector& lemma) {
        big.ensure_big(s, true);
        sort(big, lemma.begin(), lemma.end());
        uhle(big);
        if (!m_to_delete.empty()) {
            unsigned j = 0;
            for (unsigned i = 0; i < lemma.size(); ++i) {
                literal l = lemma[i];
                if (!m_to_delete.contains(l)) {
                    lemma[j++] = l;
                }
            }
            // std::cout << lemma.size() << " -> " << j << "\n";
            lemma.shrink(j);
        }
    }

    void asymm_branch::uhle(big& big) {
        m_to_delete.reset();
        if (m_to_delete.empty()) {
            int right = big.get_right(m_pos.back());
            for (unsigned i = m_pos.size() - 1; i-- > 0; ) {
                literal lit = m_pos[i];
                int right2 = big.get_right(lit);
                if (right2 > right) {
                    // lit => last, so lit can be deleted
                    m_to_delete.push_back(lit);
                }
                else {
                    right = right2;
                }
            }
        }
        if (m_to_delete.empty()) {
            int right = big.get_right(m_neg[0]);
            for (unsigned i = 1; i < m_neg.size(); ++i) {
                literal lit = m_neg[i];
                int right2 = big.get_right(lit);
                if (right > right2) {
                    // ~first => ~lit
                    m_to_delete.push_back(~lit);
                }
                else {
                    right = right2;
                }
            }
        }
    }

    bool asymm_branch::uhle(scoped_detach& scoped_d, big& big, clause & c) {
        uhle(big);
        if (!m_to_delete.empty()) {
            unsigned j = 0;
            for (unsigned i = 0; i < c.size(); ++i) {
                if (!m_to_delete.contains(c[i])) {
                    c[j] = c[i];
                    ++j;
                }
                else {
                    m_pos.erase(c[i]);
                    m_neg.erase(~c[i]);
                }
            }
            return re_attach(scoped_d, c, j);
        }
        else {
            return true;
        }
    }


    bool asymm_branch::propagate_literal(clause const& c, literal l) {
        SASSERT(!s.inconsistent());
        TRACE("asymm_branch_detail", tout << "assigning: " << l << "\n";);
        s.assign(l, justification());
        s.propagate_core(false); // must not use propagate(), since check_missed_propagation may fail for c
        return s.inconsistent();
    }

    bool asymm_branch::flip_literal_at(clause const& c, unsigned flip_index, unsigned& new_sz) {
        bool found_conflict = false;
        unsigned i = 0, sz = c.size();        
        s.push();
        for (i = 0; !found_conflict && i < sz; i++) {
            if (i == flip_index) continue;
            found_conflict = propagate_literal(c, ~c[i]);
        }
        if (!found_conflict) {
            SASSERT(sz == i);
            found_conflict = propagate_literal(c, c[flip_index]);
        }
        s.pop(1);
        new_sz = i;
        return found_conflict;
    }
    
    bool asymm_branch::cleanup(scoped_detach& scoped_d, clause& c, unsigned skip_idx, unsigned new_sz) {
        unsigned j = 0;
        for (unsigned i = 0; i < new_sz; i++) {            
            if (skip_idx == i) continue;
            literal l = c[i];
            switch (s.value(l)) {
            case l_undef:
                if (i != j) {
                    std::swap(c[i], c[j]);
                }
                j++;
                break;
            case l_false:
                break;
            case l_true:
                UNREACHABLE();
                break;
            }
        }
        new_sz = j;        
        // std::cout << "cleanup: " << c.id() << ": " << literal_vector(new_sz, c.begin()) << " delta: " << (c.size() - new_sz) << " " << skip_idx << " " << new_sz << "\n";
        return re_attach(scoped_d, c, new_sz);
    }

    bool asymm_branch::re_attach(scoped_detach& scoped_d, clause& c, unsigned new_sz) {
        m_elim_literals += c.size() - new_sz;
        if (c.is_learned()) {
            m_elim_learned_literals += c.size() - new_sz; 
        }
        switch(new_sz) {
        case 0:
            s.set_conflict(justification());
            return false;
        case 1:
            TRACE("asymm_branch", tout << "produced unit clause: " << c[0] << "\n";);
            s.assign(c[0], justification());
            s.propagate_core(false); 
            scoped_d.del_clause();
            SASSERT(s.inconsistent() || s.m_qhead == s.m_trail.size());
            return false; // check_missed_propagation() may fail, since m_clauses is not in a consistent state.
        case 2:
            SASSERT(s.value(c[0]) == l_undef && s.value(c[1]) == l_undef);
            s.mk_bin_clause(c[0], c[1], c.is_learned());
            scoped_d.del_clause();
            SASSERT(s.m_qhead == s.m_trail.size());
            return false;
        default:
            c.shrink(new_sz);
            if (s.m_config.m_drat) s.m_drat.add(c, true);
            // if (s.m_config.m_drat) s.m_drat.del(c0); // TBD
            SASSERT(s.m_qhead == s.m_trail.size());
            return true;
        }
    }

    bool asymm_branch::process_sampled(big& big, clause & c) {
        scoped_detach scoped_d(s, c);
        sort(big, c);
#if 0
        if (uhte(big, c)) {
            ++m_hidden_tautologies;
            scoped_d.del_clause();
            return false;
        }
#endif
        return uhle(scoped_d, big, c);        
    }

    bool asymm_branch::process(clause & c) {
        if (c.is_blocked()) return true;
        TRACE("asymm_branch_detail", tout << "processing: " << c << "\n";);
        SASSERT(s.scope_lvl() == 0);
        SASSERT(s.m_qhead == s.m_trail.size());
        SASSERT(!s.inconsistent());

#ifdef Z3DEBUG
        unsigned trail_sz = s.m_trail.size();
#endif
        unsigned sz = c.size();
        SASSERT(sz > 0);
        unsigned i;
        // check if the clause is already satisfied
        for (i = 0; i < sz; i++) {
            if (s.value(c[i]) == l_true) {
                s.detach_clause(c);
                s.del_clause(c);
                return false;
            }
        }
        m_counter -= c.size();

        if (m_asymm_branch_all) return process_all(c);

        // try asymmetric branching
        // clause must not be used for propagation
        scoped_detach scoped_d(s, c);
        unsigned new_sz = c.size();
        unsigned flip_position = m_rand(c.size()); 
        bool found_conflict = flip_literal_at(c, flip_position, new_sz);
        SASSERT(!s.inconsistent());
        SASSERT(s.scope_lvl() == 0);
        SASSERT(trail_sz == s.m_trail.size());
        SASSERT(s.m_qhead == s.m_trail.size());
        if (!found_conflict) {
            // clause size can't be reduced.
            return true;
        }
        else {
            // clause can be reduced 
            return cleanup(scoped_d, c, flip_position, new_sz);
        }
    }
    
    void asymm_branch::updt_params(params_ref const & _p) {
        sat_asymm_branch_params p(_p);
        m_asymm_branch         = p.asymm_branch();
        m_asymm_branch_rounds  = p.asymm_branch_rounds();
        m_asymm_branch_delay   = p.asymm_branch_delay();
        m_asymm_branch_sampled = p.asymm_branch_sampled();
        m_asymm_branch_limit   = p.asymm_branch_limit();
        m_asymm_branch_all     = p.asymm_branch_all();
        if (m_asymm_branch_limit > UINT_MAX)
            m_asymm_branch_limit = UINT_MAX;
    }

    void asymm_branch::collect_param_descrs(param_descrs & d) {
        sat_asymm_branch_params::collect_param_descrs(d);
    }
    
    void asymm_branch::collect_statistics(statistics & st) const {
        st.update("elim literals", m_elim_literals);
        st.update("hidden tautologies", m_hidden_tautologies);
    }

    void asymm_branch::reset_statistics() {
        m_elim_literals = 0;
        m_elim_learned_literals = 0;
        m_hidden_tautologies = 0;
    }

};
