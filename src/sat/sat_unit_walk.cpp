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

    2018-11-5:
      change reinitialization to use local search with limited timeouts to find phase and ordering of variables.

--*/

#include "sat_unit_walk.h"


namespace sat {

    bool_var unit_walk::var_priority::next(solver& s) {
        while (m_head < m_vars.size()) {
            bool_var v = m_vars[m_head++];
            unsigned idx = literal(v, false).index();
            if (s.m_assignment[idx] == l_undef)
                return v;            
        }
        return null_bool_var;
    }

    unit_walk::unit_walk(solver& s):
        s(s)
    {
        m_max_conflicts = 10000;
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
        init_propagation();
        init_phase();
        while (!inconsistent()) {
            if (!s.rlimit().inc()) {
                return l_undef;
            }
            bool_var v = pqueue().next(s);
            if (v == null_bool_var) {
                return l_true;
            }
            literal lit(v, !m_phase[v]);
            ++s.m_stats.m_decision;
            m_decisions.push_back(lit);
            assign(lit);
            propagate();
            while (inconsistent() && !m_decisions.empty()) {
                update_max_trail();
                ++m_conflicts;
                pop();
                propagate();
                if (m_conflicts >= m_max_conflicts) {
                    reinit_propagation();
                }
            }
        }
        return l_false;
    }


    void unit_walk::init_runs() {
        m_max_trail = 0;
        m_trail.reset();
        m_decisions.reset();
        m_phase.resize(s.num_vars());
        double2 d2;
        d2.t = 1.0;
        d2.f = 1.0;
        m_phase_tf.resize(s.num_vars(), d2);
        push_priority();
        IF_VERBOSE(1, verbose_stream() << "num vars: " << s.num_vars() << "\n";);
    }

    void unit_walk::push_priority() {
        m_ls.import(s, true);
        unsigned prefix_length = 0;
        unsigned sz = m_priorities.size();
        if (sz == m_decisions.size()) {
            prefix_length = m_trail.size();
        }
        else {
            literal last = m_decisions[sz];
            while (m_trail[prefix_length++] != last) {}
        }
        m_ls.rlimit().push(1);
        lbool is_sat = m_ls.check(prefix_length, m_trail.c_ptr(), nullptr);
        m_ls.rlimit().pop();
        TRACE("sat", tout << "result of running bounded local search " << is_sat << "\n";);
        if (is_sat == l_true) {
            IF_VERBOSE(0, verbose_stream() << "missed case of SAT\n");
        }

        m_priorities.push_back(var_priority());
        
        for (unsigned v = 0; v < s.num_vars(); ++v) {            
            if (!s.was_eliminated(v) && s.m_assignment[v] == l_undef)
                pqueue().add(v);
        }
        struct compare_break {
            local_search& ls;
            compare_break(local_search& ls): ls(ls) {}
            int operator()(bool_var v, bool_var w) const {
                double diff = ls.break_count(v) - ls.break_count(w);
                return diff > 0 ? -1 : (diff < 0 ? 1 : 0);
            }
        };
        compare_break cb(m_ls);
        std::sort(pqueue().begin(), pqueue().end(), cb);
        TRACE("sat",
              for (bool_var v : pqueue()) {
                  tout << v << " " << m_ls.break_count(v) << "\n";
              });
        
        for (bool_var v : pqueue()) {
            if (m_ls.cur_solution(v)) 
                m_phase_tf[v].t += 1;
            else
                m_phase_tf[v].f += 1;
        }
        init_phase();
    }

    void unit_walk::init_phase() {
        if (m_sticky_phase) {
            for (bool_var v : pqueue()) {
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
            for (bool_var v : pqueue()) 
                m_phase[v] = (m_rand(2) == 0); 
        }
    }

    void unit_walk::reinit_propagation() {
        IF_VERBOSE(0, verbose_stream() << "reinit-propagation\n");
        m_max_conflicts += 10000;
        if (s.m_par && s.m_par->copy_solver(s)) {
            IF_VERBOSE(1, verbose_stream() << "(sat-unit-walk fresh copy)\n";);
            if (s.get_extension()) s.get_extension()->set_unit_walk(this);
        }
        if (m_priorities.size() < m_decisions.size()) {
            pqueue().rewind(); // we will stop using this priority queue for a while.
            push_priority();
        }
    }

    void unit_walk::update_max_trail() {
        if (m_max_trail == 0 || m_trail.size() > m_max_trail) {
            m_max_trail = m_trail.size();
            log_status();
        }
    }

    void unit_walk::init_propagation() {
        if (s.m_par && s.m_par->copy_solver(s)) {
            IF_VERBOSE(1, verbose_stream() << "(sat-unit-walk fresh copy)\n";);
            if (s.get_extension()) s.get_extension()->set_unit_walk(this);
            init_runs();
            init_phase();
        }
        for (literal lit : m_trail) {
            s.m_assignment[lit.index()] = l_undef;
            s.m_assignment[(~lit).index()] = l_undef;
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
                   << " :decisions " << s.m_stats.m_decision
                   << " :propagations " << s.m_stats.m_propagate
                   << " :conflicts " << m_conflicts 
                   << ")\n";);        
    }

    literal unit_walk::choose_literal() {
        return m_trail[m_qhead++];
#if 0
        SASSERT(m_qhead < m_trail.size());
        unsigned idx = m_rand(m_trail.size() - m_qhead);
        std::swap(m_trail[m_qhead], m_trail[m_qhead + idx]);
        literal lit = m_trail[m_qhead++];
        return lit;
#endif
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

    void unit_walk::pop() {
        if (m_decisions.empty()) return;
        literal dlit = m_decisions.back();
        literal lit;
        do {
            SASSERT(!m_trail.empty());
            lit = m_trail.back(); 
            s.m_assignment[lit.index()] = l_undef;
            s.m_assignment[(~lit).index()] = l_undef;
            m_trail.pop_back();
        }
        while (lit != dlit);
        m_inconsistent = false;
        m_qhead = m_trail.size();
        assign(~dlit);
        if (m_priorities.size() == m_decisions.size()) {
            m_priorities.pop_back();
        }
        m_decisions.pop_back();
        SASSERT(m_priorities.size() <= m_decisions.size());
    }
    
};

