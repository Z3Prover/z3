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
#include "util/stopwatch.h"
#include "util/trace.h"

namespace sat {

    asymm_branch::asymm_branch(solver & _s, params_ref const & p):
        s(_s),
        m_counter(0) {
        updt_params(p);
        reset_statistics();
    }

    struct clause_size_lt {
        bool operator()(clause * c1, clause * c2) const { return c1->size() > c2->size(); }
    };

    struct asymm_branch::report {
        asymm_branch & m_asymm_branch;
        stopwatch      m_watch;
        unsigned       m_elim_literals;
        report(asymm_branch & a):
            m_asymm_branch(a),
            m_elim_literals(a.m_elim_literals) {
            m_watch.start();
        }
        
        ~report() {
            m_watch.stop();
            IF_VERBOSE(SAT_VB_LVL, 
                       verbose_stream() << " (sat-asymm-branch :elim-literals "
                       << (m_asymm_branch.m_elim_literals - m_elim_literals)
                       << " :cost " << m_asymm_branch.m_counter
                       << mem_stat()
                       << " :time " << std::fixed << std::setprecision(2) << m_watch.get_seconds() << ")\n";);
        }
    };
    
    void asymm_branch::operator()(bool force) {
        if (!m_asymm_branch && !m_asymm_branch_all)
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
        m_counter  = 0; 
        int64 limit = -m_asymm_branch_limit;
        std::stable_sort(s.m_clauses.begin(), s.m_clauses.end(), clause_size_lt());
        m_counter -= s.m_clauses.size();
        SASSERT(s.m_qhead == s.m_trail.size());
        clause_vector::iterator it  = s.m_clauses.begin();
        clause_vector::iterator it2 = it;
        clause_vector::iterator end = s.m_clauses.end();
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
                if (!process(c))
                    continue; // clause was removed
                *it2 = *it;
                ++it2;
            }
            s.m_clauses.set_end(it2);
        }
        catch (solver_exception & ex) {
            // put m_clauses in a consistent state...
            for (; it != end; ++it, ++it2) {
                *it2 = *it;
            }
            s.m_clauses.set_end(it2);
            m_counter = -m_counter;
            throw ex;
        }
        m_counter = -m_counter;
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
        m_elim_literals += c.size() - new_sz;
        // std::cout << "cleanup: " << c.id() << ": " << literal_vector(new_sz, c.begin()) << " delta: " << (c.size() - new_sz) << " " << skip_idx << " " << new_sz << "\n";
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
            s.mk_bin_clause(c[0], c[1], false);
            scoped_d.del_clause();
            SASSERT(s.m_qhead == s.m_trail.size());
            return false;
        default:
            c.shrink(new_sz);
            s.attach_clause(c);
            if (s.m_config.m_drat) s.m_drat.add(c, true);
            // if (s.m_config.m_drat) s.m_drat.del(c0); // TBD
            SASSERT(s.m_qhead == s.m_trail.size());
            return true;
        }
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
        unsigned flip_position = 2 + m_rand(c.size() - 2); // don't flip on the watch literals.
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
        m_asymm_branch        = p.asymm_branch();
        m_asymm_branch_limit  = p.asymm_branch_limit();
        m_asymm_branch_all    = p.asymm_branch_all();
        if (m_asymm_branch_limit > UINT_MAX)
            m_asymm_branch_limit = UINT_MAX;
    }

    void asymm_branch::collect_param_descrs(param_descrs & d) {
        sat_asymm_branch_params::collect_param_descrs(d);
    }
    
    void asymm_branch::collect_statistics(statistics & st) const {
        st.update("elim literals", m_elim_literals);
    }

    void asymm_branch::reset_statistics() {
        m_elim_literals = 0;
    }

};
