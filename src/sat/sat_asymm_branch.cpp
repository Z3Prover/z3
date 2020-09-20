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
        m_touch_index = 0;
    }

    struct clause_size_lt {
        bool operator()(clause * c1, clause * c2) const { return c1->size() > c2->size(); }
    };

    struct asymm_branch::report {
        asymm_branch & m_asymm_branch;
        stopwatch      m_watch;
        unsigned       m_elim_literals;
        unsigned       m_elim_learned_literals;
        unsigned       m_tr;
        unsigned       m_units;
        report(asymm_branch & a):
            m_asymm_branch(a),
            m_elim_literals(a.m_elim_literals),
            m_elim_learned_literals(a.m_elim_learned_literals),            
            m_tr(a.m_tr),
            m_units(a.s.init_trail_size()) {
            m_watch.start();
        }
        
        ~report() {
            m_watch.stop();
            IF_VERBOSE(2,
                       unsigned num_learned = (m_asymm_branch.m_elim_learned_literals - m_elim_learned_literals);
                       unsigned num_total = (m_asymm_branch.m_elim_literals - m_elim_literals);
                       unsigned num_units = (m_asymm_branch.s.init_trail_size() - m_units);
                       unsigned elim_lits = (num_total - num_learned);
                       unsigned tr = (m_asymm_branch.m_tr - m_tr);
                       verbose_stream() << " (sat-asymm-branch";
                       if (elim_lits > 0)   verbose_stream() << " :elim-literals " << elim_lits; 
                       if (num_learned > 0) verbose_stream() << " :elim-learned-literals " << num_learned;
                       if (num_units > 0)   verbose_stream() << " :units " << num_units;
                       if (tr > 0)          verbose_stream() << " :hte " << tr;
                       verbose_stream() << " :cost " << m_asymm_branch.m_counter;
                       verbose_stream() << mem_stat();
                       verbose_stream() << m_watch << ")\n";);
        }
    };

    void asymm_branch::process_bin(big& big) {
        m_tr += big.reduce_tr(s);
    }

    bool asymm_branch::process(big& big, bool learned) {
        unsigned elim0 = m_elim_literals;
        unsigned eliml0 = m_elim_learned_literals;
        for (unsigned i = 0; i < m_asymm_branch_rounds; ++i) {
            unsigned elim = m_elim_literals + m_tr;
            big.init(s, learned);
            process(&big, s.m_clauses);
            process(&big, s.m_learned);
            process_bin(big);
            s.propagate(false); 
            if (s.m_inconsistent)
                break;
            unsigned num_elim = m_elim_literals + m_tr - elim;
            IF_VERBOSE(4, verbose_stream() << "(sat-asymm-branch-step :elim " << num_elim << ")\n";);
            if (num_elim == 0)
                break;
        }        
        IF_VERBOSE(4, if (m_elim_learned_literals > eliml0) 
                          verbose_stream() << "(sat-asymm-branch :elim " << m_elim_learned_literals - eliml0 << ")\n";);
        return m_elim_literals > elim0;
    }

    bool asymm_branch::process(bool learned) {
        unsigned eliml0 = m_elim_learned_literals;
        unsigned elim = m_elim_literals;
        process(nullptr, s.m_clauses);
        if (learned) process(nullptr, s.m_learned);
        s.propagate(false); 
        IF_VERBOSE(4, if (m_elim_learned_literals > eliml0) 
                          verbose_stream() << "(sat-asymm-branch :elim " << m_elim_learned_literals - eliml0 << ")\n";);
        return m_elim_literals > elim;
    }


    void asymm_branch::process(big* big, clause_vector& clauses) {
        int64_t limit = -m_asymm_branch_limit;
        std::stable_sort(clauses.begin(), clauses.end(), clause_size_lt());
        m_counter -= clauses.size();
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
                clause & c = *(*it);
                if (m_counter < limit || s.inconsistent() || c.was_removed()) {
                    *it2 = *it;
                    ++it2;
                    continue;
                }
                s.checkpoint();                
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
        bool_vector saved_phase(s.m_phase);
        flet<bool> _is_probing(s.m_is_probing, true);

        bool change = true;
        unsigned counter = 0;
        while (change && counter < 2) {
            ++counter;
            change = false;
            s.m_touch_index++;
            if (m_asymm_branch_sampled) {
                big big(s.m_rand);
                if (process(big, true)) change = true;
            }
            if (m_asymm_branch_sampled) {
                big big(s.m_rand);
                if (process(big, false)) change = true;
            }
            if (m_asymm_branch) {
                m_counter  = 0; 
                if (process(false)) change = true;
                m_counter = -m_counter;
            }
            m_touch_index = s.m_touch_index;
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

    bool asymm_branch::is_touched(bool_var v) const { 
        return s.m_touched[v] >= m_touch_index; 
    }

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

        IF_VERBOSE(100, 
                   for (literal l : m_pos) verbose_stream() << big.get_left(l) << " "; 
                   verbose_stream() << "\n";
                   for (literal l : m_neg) verbose_stream() << big.get_left(l) << " "; 
                   verbose_stream() << "\n";
                   );
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
                literal lit = c[i];
                switch (s.value(lit)) {
                case l_true:
                    scoped_d.del_clause();
                    return false;
                case l_false:    
                    break;
                default:
                    if (!m_to_delete.contains(lit)) {
                        if (i != j) {
                            std::swap(c[i], c[j]);
                        }
                        j++;
                    }
                    break;
                }
            }
            return re_attach(scoped_d, c, j);
        }
        else {
            return true;
        }
    }


    bool asymm_branch::propagate_literal(clause const& c, literal l) {
        if (!is_touched(l.var())) {
            return false;
        }
        SASSERT(!s.inconsistent());
        TRACE("asymm_branch_detail", tout << "assigning: " << l << "\n";);
        s.assign_scoped(l);
        s.propagate_core(false); // must not use propagate(), since check_missed_propagation may fail for c
        return s.inconsistent();
    }

    bool asymm_branch::flip_literal_at(clause const& c, unsigned flip_index, unsigned& new_sz) {
        VERIFY(s.m_trail.size() == s.m_qhead);
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
        return re_attach(scoped_d, c, new_sz);
    }

    bool asymm_branch::re_attach(scoped_detach& scoped_d, clause& c, unsigned new_sz) {
        VERIFY(s.m_trail.size() == s.m_qhead);
        unsigned old_sz = c.size();
        m_elim_literals += old_sz - new_sz;
        if (c.is_learned()) {
            m_elim_learned_literals += old_sz - new_sz; 
        }

        switch (new_sz) {
        case 0:
            s.set_conflict();
            return false;
        case 1:
            TRACE("asymm_branch", tout << "produced unit clause: " << c[0] << "\n";);
            s.assign_unit(c[0]);
            s.propagate_core(false); 
            scoped_d.del_clause();
            return false; // check_missed_propagation() may fail, since m_clauses is not in a consistent state.
        case 2:
            SASSERT(s.value(c[0]) == l_undef && s.value(c[1]) == l_undef);
            VERIFY(s.value(c[0]) == l_undef && s.value(c[1]) == l_undef);
            s.mk_bin_clause(c[0], c[1], c.is_learned());
            if (s.m_trail.size() > s.m_qhead) s.propagate_core(false);
            scoped_d.del_clause();
            return false;
        default:
            s.shrink(c, old_sz, new_sz);
            return true;
        }
    }

    bool asymm_branch::process_sampled(big& big, clause & c) {
        scoped_detach scoped_d(s, c);
        sort(big, c);
        if (uhte(big, c)) {
            // don't touch hidden tautologies. 
            // ATE takes care of them.
            return true;
        }
        return uhle(scoped_d, big, c);        
    }

    bool asymm_branch::process(clause & c) {
        TRACE("asymm_branch_detail", tout << "processing: " << c << "\n";);
        SASSERT(s.scope_lvl() == 0);
        SASSERT(!s.inconsistent());

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
        st.update("sat elim literals", m_elim_literals);
        st.update("sat tr", m_tr);
    }

    void asymm_branch::reset_statistics() {
        m_elim_literals = 0;
        m_elim_learned_literals = 0;
        m_tr = 0;
    }

};
