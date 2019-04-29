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

    It does not attempt to add conflict clauses 

    It can receive conflict clauses from a concurrent CDCL solver 

    The phase of variables is optionally sticky between rounds. We use a decay rate
    to compute stickiness of a variable.

Author:

    Nikolaj Bjorner (nbjorner) 2017-12-15.

Revision History:

    2018-11-5:
      change reinitialization to use local search with limited timeouts to find phase and ordering of variables.

--*/

#include "sat/sat_unit_walk.h"
#include "util/luby.h"


namespace sat {

    bool_var unit_walk::var_priority::peek(solver& s) {
        while (m_head < m_vars.size()) {
            bool_var v = m_vars[m_head];
            unsigned idx = literal(v, false).index();
            if (s.m_assignment[idx] == l_undef) {
                // IF_VERBOSE(0, verbose_stream() << "pop " << v << "\n");
                return v;            
            }
            ++m_head;
        }
        for (bool_var v : m_vars) {
            if (s.m_assignment[literal(v, false).index()] == l_undef) {
                IF_VERBOSE(0, verbose_stream() << "unassigned: " << v << "\n");
            }
        }
        IF_VERBOSE(0, verbose_stream() << "#vars: " << m_vars.size() << "\n");
        IF_VERBOSE(0, verbose_stream() << "(sat.unit-walk sat)\n");
        return null_bool_var;
    }

    void unit_walk::var_priority::set_vars(solver& s) {
        m_vars.reset();
        s.pop_to_base_level();

        for (unsigned v = 0; v < s.num_vars(); ++v) {            
            if (!s.was_eliminated(v) && s.value(v) == l_undef) {
                add(v);
            }
        }
        IF_VERBOSE(0, verbose_stream() << "num vars " << m_vars.size() << "\n";);
    }

    bool_var unit_walk::var_priority::next(solver& s) {
        bool_var v = peek(s);
        ++m_head;
        return v;
    }

    unit_walk::unit_walk(solver& s):
        s(s) {
        m_max_conflicts = 10000;
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
        lbool st = l_undef;
        while (s.rlimit().inc() && st == l_undef) {
            if (inconsistent() && !m_decisions.empty()) do_pop();
            else if (inconsistent()) st = l_false; 
            else if (should_restart()) restart();
            else if (should_backjump()) st = do_backjump();
            else st = decide();
        }
        log_status();
        return st;
    }

    void unit_walk::do_pop() {
        update_max_trail();
        ++s.m_stats.m_conflict;
        pop();
        propagate();
    }

    lbool unit_walk::decide() {
        bool_var v = pqueue().next(s);
        if (v == null_bool_var) {
            return l_true;
        }
        literal lit(v, !m_phase[v]);
        ++s.m_stats.m_decision;
        m_decisions.push_back(lit);
        pqueue().push();
        assign(lit);
        propagate();
        return l_undef;
    }

    bool unit_walk::should_backjump() {
        return 
            s.m_stats.m_conflict >= m_max_conflicts && m_decisions.size() > 20;
    } 

    lbool unit_walk::do_backjump() {
        unsigned backjump_level = m_decisions.size(); // - (m_decisions.size()/20);
        switch (update_priority(backjump_level)) {
        case l_true: return l_true;
        case l_false: break; // TBD
        default: break;
        }
        refresh_solver();
        return l_undef;
    }

    void unit_walk::pop() {
        SASSERT (!m_decisions.empty());
        literal dlit = m_decisions.back();
        pop_decision();
        assign(~dlit);
    }

    void unit_walk::pop_decision() {
        SASSERT (!m_decisions.empty());
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
        m_qhead = m_trail.size();
        m_decisions.pop_back();
        pqueue().pop();
        m_inconsistent = false;
    }

    void unit_walk::init_runs() {
        m_luby_index = 0;
        m_restart_threshold = 1000;
        m_max_trail = 0;
        m_trail.reset();
        m_decisions.reset();
        m_phase.resize(s.num_vars());
        m_phase_tf.resize(s.num_vars(), ema(1e-5));
        pqueue().reset();
        pqueue().set_vars(s);
        for (unsigned v = 0; v < s.num_vars(); ++v) {            
            m_phase_tf[v].update(50);
        }
        m_ls.import(s, true);
        m_rand.set_seed(s.rand()());
        update_priority(0);
    }

    lbool unit_walk::do_local_search(unsigned num_rounds) {
        unsigned prefix_length = (0*m_trail.size())/10;
        for (unsigned v = 0; v < s.num_vars(); ++v) {
            m_ls.set_bias(v, m_phase_tf[v] >= 50 ? l_true : l_false);
        }
        for (literal lit : m_trail) {
            m_ls.set_bias(lit.var(), lit.sign() ? l_false : l_true);
        }
        m_ls.rlimit().push(num_rounds);
        lbool is_sat = m_ls.check(prefix_length, m_trail.c_ptr(), nullptr);
        m_ls.rlimit().pop();
        return is_sat;
    }

    lbool unit_walk::update_priority(unsigned level) {

        while (m_decisions.size() > level) {
            pop_decision();
        }
        IF_VERBOSE(1, verbose_stream() << "(sat.unit-walk :update-priority " << m_decisions.size() << "\n");

        unsigned num_rounds = 50;
        log_status();

        lbool is_sat = do_local_search(num_rounds);
        switch (is_sat) {
        case l_true:
            for (unsigned v = 0; v < s.num_vars(); ++v) {
                s.m_assignment[v] = m_ls.get_best_phase(v) ? l_true : l_false;
            } 
            return l_true;
        case l_false:
            if (m_decisions.empty()) {
                return l_false;
            }
            else {
                pop();
                return l_undef;
            }
        default:
            update_pqueue();
            return l_undef;
        }        
    }

    /**
     * \brief Reshuffle variables in the priority queue using the break counts from local search.
     */
    struct compare_break {
        local_search& ls;
        compare_break(local_search& ls): ls(ls) {}
        int operator()(bool_var v, bool_var w) const {
            return ls.get_priority(v) > ls.get_priority(w);
        }
    };

    void unit_walk::update_pqueue() {
        compare_break cb(m_ls);
        std::sort(pqueue().begin(), pqueue().end(), cb);        
        for (bool_var v : pqueue()) {
            m_phase_tf[v].update(m_ls.cur_solution(v) ? 100 : 0);
            m_phase[v] = l_true == m_ls.cur_solution(v);
        }
        pqueue().rewind();
    }

    void unit_walk::init_phase() {
        for (bool_var v : pqueue()) {
            m_phase[v] = s.m_phase[v];            
        }
    }

    void unit_walk::refresh_solver() {
        m_max_conflicts += m_conflict_offset ;
        m_conflict_offset += 10000;
        if (s.m_par && s.m_par->copy_solver(s)) {
            IF_VERBOSE(1, verbose_stream() << "(sat.unit-walk fresh copy)\n";);
            if (s.get_extension()) s.get_extension()->set_unit_walk(this);
            init_runs();
            init_phase();
        }
    }

    bool unit_walk::should_restart() {
        if (s.m_stats.m_conflict >= m_restart_threshold) {
            m_restart_threshold = s.get_config().m_restart_initial * get_luby(m_luby_index);
            ++m_luby_index;
            return true;
        }
        return false;        
    }

    void unit_walk::restart() {
        while (!m_decisions.empty()) {
            pop_decision();
        }
    }

    void unit_walk::update_max_trail() {
        if (m_max_trail == 0 || m_trail.size() > m_max_trail) {
            m_max_trail = m_trail.size();
            m_restart_threshold += 10000;
            m_max_conflicts = s.m_stats.m_conflict + 20000;
            log_status();
        }
    }

    void unit_walk::init_propagation() {
        if (s.m_par && s.m_par->copy_solver(s)) {
            IF_VERBOSE(1, verbose_stream() << "(sat.unit-walk fresh copy)\n";);
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
        s.m_stats.m_conflict = 0;
        m_conflict_offset = 10000;
        m_decisions.reset();
        m_qhead = 0;
        m_inconsistent = false;
    }

    void unit_walk::propagate() {
        while (m_qhead < m_trail.size() && !inconsistent()) {
            propagate(m_trail[m_qhead++]);         
        }
    }

    std::ostream& unit_walk::display(std::ostream& out) const {
        unsigned i = 0;
        out << "num decisions: " << m_decisions.size() << "\n";
        for (literal lit : m_trail) {
            if (i < m_decisions.size() && m_decisions[i] == lit) {
                out << "d " << i << ": ";
                ++i;
            }
            out << lit << "\n";
        }
        s.display(verbose_stream());
        return out;
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
        VERIFY(value(lit) == l_undef);
        s.m_assignment[lit.index()] = l_true;
        s.m_assignment[(~lit).index()] = l_false;
        m_trail.push_back(lit);
        if (s.get_extension() && s.is_external(lit.var())) {
            s.get_extension()->asserted(lit);       
        } 
        if (m_phase[lit.var()] == lit.sign()) {
            ++m_flips;
            flip_phase(lit);
            m_phase_tf[lit.var()].update(m_phase[lit.var()] ? 100 : 0);        
        }
    }

    void unit_walk::flip_phase(literal l) {
        bool_var v = l.var();
        m_phase[v] = !m_phase[v]; 
    }

    void unit_walk::log_status() {
        IF_VERBOSE(1, verbose_stream() 
                   << "(sat.unit-walk"
                   << " :trail " << m_trail.size()
                   << " :depth " << m_decisions.size()
                   << " :decisions " << s.m_stats.m_decision
                   << " :propagations " << s.m_stats.m_propagate
                   << " :conflicts " << s.m_stats.m_conflict 
                   << ")\n";);        
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
    
};

