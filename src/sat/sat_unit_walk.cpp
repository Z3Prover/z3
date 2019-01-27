/*++
Copyright (c) 2017 Microsoft Corporation

Module Name:

    sat_unit_walk.cpp

Abstract:

    unit walk local search procedure.
    A variant of UnitWalk. Hirsch and Kojevinkov, SAT 2001.
    This version uses a trail to reset assignments and integrates directly with the 
    watch list structure. Thus, assignments are not delayed and we avoid treating
    pending units as a multi-set. 

    It uses standard DPLL approach for backracking, flipping the last decision literal that
    lead to a conflict. It restarts after evern 100 conflicts.

    It does not attempt to add conflict clauses or alternate with
    walksat.

    It can receive conflict clauses from a concurrent CDCL solver and does not
    create its own conflict clauses.

    The phase of variables is optionally sticky between rounds. We use a decay rate
    to compute stickiness of a variable.

Author:

    Nikolaj Bjorner (nbjorner) 2017-12-15.

Revision History:

--*/

#include "sat_unit_walk.h"

namespace sat {

    unit_walk::unit_walk(solver& s):
        s(s)
    {
        m_runs = 0;
        m_periods = 0;
        m_max_runs = UINT_MAX;
        m_max_periods = 5000; // UINT_MAX; // TBD configure
        m_max_conflicts = 100;
        m_sticky_phase = s.get_config().m_phase_sticky;
        m_flips = 0;
    }                        

    class scoped_set_unit_walk {
        solver& s;
    public:
        scoped_set_unit_walk(unit_walk* u, solver& s): s(s) {
            if (s.get_extension()) s.get_extension()->set_unit_walk(u);
        }
        ~scoped_set_unit_walk() {
            if (s.get_extension()) s.get_extension()->set_unit_walk(nullptr);
        }
    };

    lbool unit_walk::operator()() {
        scoped_set_unit_walk _scoped_set(this, s);
        init_runs();
        for (m_runs = 0; m_runs < m_max_runs || m_max_runs == UINT_MAX; ++m_runs) {
            init_propagation();
            init_phase();
            for (m_periods = 0; m_periods < m_max_periods || m_max_periods == UINT_MAX; ++m_periods) {
                if (!s.rlimit().inc()) return l_undef;
                lbool r = unit_propagation();
                if (r != l_undef) return r;                
            }        
        }
        return l_undef;
    }

    lbool unit_walk::unit_propagation() {
        init_propagation();     
        while (!m_freevars.empty() && !inconsistent()) {
            bool_var v = m_freevars.begin()[m_rand(m_freevars.size())];
            literal lit(v, !m_phase[v]);
            ++s.m_stats.m_decision;
            m_decisions.push_back(lit);
            assign(lit);
            propagate();
            while (inconsistent() && !m_decisions.empty()) {
                ++m_conflicts;
                backtrack();
                propagate();
            }
            if (m_conflicts >= m_max_conflicts && !m_freevars.empty()) {
                set_conflict();
                break;
            }
        }
        if (!inconsistent()) {
            log_status();
            IF_VERBOSE(1, verbose_stream() << "(sat-unit-walk sat)\n";);
            s.mk_model();
            return l_true;
        }
        return l_undef;
    }

    void unit_walk::init_runs() {
        m_freevars.reset();
        m_trail.reset();
        m_decisions.reset();
        m_phase.resize(s.num_vars());
        double2 d2;
        d2.t = 1.0;
        d2.f = 1.0;
        m_phase_tf.resize(s.num_vars(), d2);
        for (unsigned i = 0; i < s.num_vars(); ++i) {
            literal l(i, false);
            if (!s.was_eliminated(l.var()) && s.m_assignment[l.index()] == l_undef)
                m_freevars.insert(l.var());
        }
        IF_VERBOSE(1, verbose_stream() << "num vars: " << s.num_vars() << " free vars: " << m_freevars.size() << "\n";);
    }

    void unit_walk::init_phase() {
        m_max_trail = 0;
        if (m_sticky_phase) {
            for (bool_var v : m_freevars) {
                if (s.m_phase[v] == POS_PHASE) {
                    m_phase[v] = true;
                }
                else if (s.m_phase[v] == NEG_PHASE) {
                    m_phase[v] = false;
                }
                else {
                    m_phase[v] = m_rand(100 * static_cast<unsigned>(m_phase_tf[v].t + m_phase_tf[v].f)) <= 100 * m_phase_tf[v].t;
                }
            }
        }
        else {
            for (bool_var v : m_freevars) 
                m_phase[v] = (m_rand(2) == 0); 
        }
    }

    void unit_walk::init_propagation() {
        if (s.m_par && s.m_par->copy_solver(s)) {
            IF_VERBOSE(1, verbose_stream() << "(sat-unit-walk fresh copy)\n";);
            if (s.get_extension()) s.get_extension()->set_unit_walk(this);
            init_runs();
            init_phase();
        }
        if (m_max_trail == 0 || m_trail.size() > m_max_trail) {
            m_max_trail = m_trail.size();
            log_status();
        }
        for (literal lit : m_trail) {
            s.m_assignment[lit.index()] = l_undef;
            s.m_assignment[(~lit).index()] = l_undef;
            m_freevars.insert(lit.var());
        }
        m_flips = 0;
        m_trail.reset();
        m_conflicts = 0;
        m_decisions.reset();
        m_qhead = 0;
        m_inconsistent = false;
    }

    void unit_walk::propagate() {
        while (m_qhead < m_trail.size() && !inconsistent()) 
            propagate(choose_literal());            
        // IF_VERBOSE(1, verbose_stream() << m_trail.size() << " " << inconsistent() << "\n";);
    }

    void unit_walk::propagate(literal l) {
        ++s.m_stats.m_propagate;
        literal not_l = ~l;
        literal l1, l2;
        lbool val1, val2;
        bool keep;
        watch_list & wlist = s.get_wlist(l);
        watch_list::iterator it  = wlist.begin();
        watch_list::iterator it2 = it;
        watch_list::iterator end = wlist.end();
        for (; it != end; ++it) {
            switch (it->get_kind()) {
            case watched::BINARY:
                l1 = it->get_literal();
                switch (value(l1)) {
                case l_false:
                    conflict_cleanup(it, it2, wlist);
                    set_conflict(l,l1);
                    return;
                case l_undef:
                    assign(l1);
                    break;
                case l_true:
                    break; // skip
                }
                *it2 = *it;
                it2++;
                break;
            case watched::TERNARY:
                l1 = it->get_literal1();
                l2 = it->get_literal2();
                val1 = value(l1);
                val2 = value(l2);
                if (val1 == l_false && val2 == l_undef) {
                    assign(l2);
                }
                else if (val1 == l_undef && val2 == l_false) {
                    assign(l1);
                }
                else if (val1 == l_false && val2 == l_false) {
                    conflict_cleanup(it, it2, wlist);
                    set_conflict(l,l1,l2);
                    return;
                }
                *it2 = *it;
                it2++;
                break;
            case watched::CLAUSE: {
                if (value(it->get_blocked_literal()) == l_true) {
                    *it2 = *it;
                    it2++;
                    break;
                }
                clause_offset cls_off = it->get_clause_offset();
                clause & c = s.get_clause(cls_off);
                if (c[0] == not_l)
                    std::swap(c[0], c[1]);
                if (c[1] != not_l) {
                    *it2 = *it;
                    it2++;
                    break;
                }
                if (value(c[0]) == l_true) {
                    it2->set_clause(c[0], cls_off);
                    it2++;
                    break;
                }
                SASSERT(c[1] == not_l);
                literal * l_it  = c.begin() + 2;
                literal * l_end = c.end();
                for (; l_it != l_end; ++l_it) {
                    if (value(*l_it) != l_false) {
                        c[1]  = *l_it;
                        *l_it = not_l;
                        s.get_wlist((~c[1]).index()).push_back(watched(c[0], cls_off));
                        goto end_clause_case;
                    }
                }
                SASSERT(value(c[0]) == l_false || value(c[0]) == l_undef);
                if (value(c[0]) == l_false) {
                    c.mark_used();
                    conflict_cleanup(it, it2, wlist);
                    set_conflict(c);
                    return;
                }
                else {
                    *it2 = *it;
                    it2++;
                    assign(c[0]);
                }
                end_clause_case:
                break;
            }
            case watched::EXT_CONSTRAINT:
                SASSERT(s.get_extension());
                keep = s.get_extension()->propagate(l, it->get_ext_constraint_idx());
                if (inconsistent()) {
                    if (!keep) {
                        ++it;
                    }
                    set_conflict(l, l);
                    conflict_cleanup(it, it2, wlist);
                    return;
                }
                if (keep) {
                    *it2 = *it;
                    it2++;
                }
                break;
            default:
                UNREACHABLE();
                break;
            }
        }
        wlist.set_end(it2);
    }

    void unit_walk::assign(literal lit) {
        SASSERT(value(lit) == l_undef);
        s.m_assignment[lit.index()] = l_true;
        s.m_assignment[(~lit).index()] = l_false;
        m_trail.push_back(lit);
        m_freevars.remove(lit.var());
        if (s.get_extension() && s.is_external(lit.var())) {
            s.get_extension()->asserted(lit);       
        } 
        if (m_phase[lit.var()] == lit.sign()) {
            ++m_flips;
            flip_phase(lit);
        }
    }

    void unit_walk::flip_phase(literal l) {
        bool_var v = l.var();
        m_phase[v] = !m_phase[v]; 
        if (m_sticky_phase) {
            m_phase_tf[v].f *= 0.98;
            m_phase_tf[v].t *= 0.98;
            if (m_phase[v]) m_phase_tf[v].t += 1; else m_phase_tf[v].f += 1;
        }
    }

    void unit_walk::log_status() {
        IF_VERBOSE(1, verbose_stream() << "(sat-unit-walk :trail " << m_max_trail 
                   << " :branches " << m_decisions.size()
                   << " :free " << m_freevars.size() 
                   << " :periods " << m_periods                    
                   << " :decisions " << s.m_stats.m_decision
                   << " :propagations " << s.m_stats.m_propagate
                   << ")\n";);        
    }

    literal unit_walk::choose_literal() {
        SASSERT(m_qhead < m_trail.size());
        unsigned idx = m_rand(m_trail.size() - m_qhead);
        std::swap(m_trail[m_qhead], m_trail[m_qhead + idx]);
        literal lit = m_trail[m_qhead++];
        return lit;
    }

    void unit_walk::set_conflict(literal l1, literal l2) {
        set_conflict();
    }

    void unit_walk::set_conflict(literal l1, literal l2, literal l3) {
        set_conflict();
    }

    void unit_walk::set_conflict(clause const& c) {
        set_conflict();
    }

    void unit_walk::set_conflict() {
        m_inconsistent = true; 
    }

    void unit_walk::backtrack() {
        if (m_decisions.empty()) return;
        literal dlit = m_decisions.back();
        literal lit;
        do {
            SASSERT(!m_trail.empty());
            lit = m_trail.back(); 
            s.m_assignment[lit.index()] = l_undef;
            s.m_assignment[(~lit).index()] = l_undef;
            m_freevars.insert(lit.var());            
            m_trail.pop_back();
        }
        while (lit != dlit);
        m_inconsistent = false;
        m_decisions.pop_back();
        m_qhead = m_trail.size();
        assign(~dlit);
    }
    
};

