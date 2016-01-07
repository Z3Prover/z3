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
#include"sat_asymm_branch.h"
#include"sat_asymm_branch_params.hpp"
#include"sat_solver.h"
#include"stopwatch.h"
#include"trace.h"

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
        if (!m_asymm_branch)
            return;
        s.propagate(false); // must propagate, since it uses s.push()
        if (s.m_inconsistent)
            return;
        if (!force && m_counter > 0)
            return;
        CASSERT("asymm_branch", s.check_invariant());
        TRACE("asymm_branch_detail", s.display(tout););
        report rpt(*this);
        svector<char> saved_phase(s.m_phase);
        m_counter  = 0; // counter is moving down to capture propagate cost.
        int limit  = -static_cast<int>(m_asymm_branch_limit);
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
                m_counter -= c.size();
                if (!process(c))
                    continue; // clause was removed
                *it2 = *it;
                // throw exception to test bug fix: if (it2 != it) throw solver_exception("trigger bug");
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
        CASSERT("asymm_branch", s.check_invariant());
    }

    bool asymm_branch::process(clause & c) {
        TRACE("asymm_branch_detail", tout << "processing: " << c << "\n";);
        SASSERT(s.scope_lvl() == 0);
        SASSERT(s.m_qhead == s.m_trail.size());
#ifdef Z3DEBUG
        unsigned trail_sz = s.m_trail.size();
#endif
        SASSERT(!s.inconsistent());
        unsigned sz = c.size();
        SASSERT(sz > 0);
        unsigned i;
        // check if the clause is already satisfied
        for (i = 0; i < sz; i++) {
            if (s.value(c[i]) == l_true) {
                s.dettach_clause(c);
                s.del_clause(c);
                return false;
            }
        }
        // try asymmetric branching
        // clause must not be used for propagation
        s.dettach_clause(c);
        s.push();
        for (i = 0; i < sz - 1; i++) {
            literal l = c[i];
            SASSERT(!s.inconsistent());
            TRACE("asymm_branch_detail", tout << "assigning: " << ~l << "\n";);
            s.assign(~l, justification());
            s.propagate_core(false); // must not use propagate(), since check_missed_propagation may fail for c
            if (s.inconsistent())
                break;
        }
        s.pop(1);
        SASSERT(!s.inconsistent());
        SASSERT(s.scope_lvl() == 0);
        SASSERT(trail_sz == s.m_trail.size());
        SASSERT(s.m_qhead == s.m_trail.size());
        if (i == sz - 1) {
            // clause size can't be reduced.
            s.attach_clause(c);
            return true;
        }
        // clause can be reduced 
        unsigned new_sz = i+1;
        SASSERT(new_sz >= 1);
        SASSERT(new_sz < sz);
        TRACE("asymm_branch", tout << c << "\nnew_size: " << new_sz << "\n";
              for (unsigned i = 0; i < c.size(); i++) tout << static_cast<int>(s.value(c[i])) << " "; tout << "\n";);
        // cleanup reduced clause
        unsigned j = 0;
        for (i = 0; i < new_sz; i++) {
            literal l = c[i];
            switch (s.value(l)) {
            case l_undef:
                c[j] = l;
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
        m_elim_literals += sz - new_sz;
        switch(new_sz) {
        case 0:
            s.set_conflict(justification());
            return false;
        case 1:
            TRACE("asymm_branch", tout << "produced unit clause: " << c[0] << "\n";);
            s.assign(c[0], justification());
            s.del_clause(c);
            s.propagate_core(false); 
            SASSERT(s.inconsistent() || s.m_qhead == s.m_trail.size());
            return false; // check_missed_propagation() may fail, since m_clauses is not in a consistent state.
        case 2:
            SASSERT(s.value(c[0]) == l_undef && s.value(c[1]) == l_undef);
            s.mk_bin_clause(c[0], c[1], false);
            s.del_clause(c);
            SASSERT(s.m_qhead == s.m_trail.size());
            return false;
        default:
            c.shrink(new_sz);
            s.attach_clause(c);
            SASSERT(s.m_qhead == s.m_trail.size());
            return true;
        }
    }
    
    void asymm_branch::updt_params(params_ref const & _p) {
        sat_asymm_branch_params p(_p);
        m_asymm_branch        = p.asymm_branch();
        m_asymm_branch_rounds = p.asymm_branch_rounds();
        m_asymm_branch_limit  = p.asymm_branch_limit();
        if (m_asymm_branch_limit > INT_MAX)
            m_asymm_branch_limit = INT_MAX;
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
