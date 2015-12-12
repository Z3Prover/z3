/*++
Copyright (c) 2014 Microsoft Corporation

Module Name:

    sat_mus.cpp

Abstract:
   
    Faster MUS extraction

Author:

    Nikolaj Bjorner (nbjorner) 2014-20-7

Notes:


--*/

#include "sat_solver.h"
#include "sat_mus.h"
#include "sat_sls.h"

namespace sat {

    mus::mus(solver& s):s(s), m_is_active(false), m_best_value(0), m_restart(0), m_max_restarts(0) {}

    mus::~mus() {}
   
    void mus::reset() {
        m_core.reset();
        m_mus.reset();
        m_model.reset();
        m_best_value = 0;
        m_max_restarts = (s.m_stats.m_restart - m_restart) + 10;
        m_restart = s.m_stats.m_restart;
    }

    void mus::set_core() {   
        m_mus.append(m_core);
        s.m_core.reset();
        s.m_core.append(m_mus);
        TRACE("sat", tout << "new core: " << s.m_core << "\n";);
    }

    void mus::update_model() {
        double new_value = s.m_wsls.evaluate_model(s.m_model);
        if (m_model.empty()) {
            m_model.append(s.m_model);
            m_best_value = new_value;
        }
        else if (m_best_value > new_value) {
            m_model.reset();
            m_model.append(s.m_model);
            m_best_value = new_value;
        }
    }

    lbool mus::operator()() {
        flet<bool> _disable_min(s.m_config.m_minimize_core, false);
        flet<bool> _disable_opt(s.m_config.m_optimize_model, false);
        flet<bool> _is_active(m_is_active, true);
        IF_VERBOSE(3, verbose_stream() << "(sat.mus " << s.get_core() << ")\n";);
        reset();
        lbool r = mus1();
        m_restart = s.m_stats.m_restart;
        return r;
    }

    lbool mus::mus1() {
        bool minimize_partial = s.m_config.m_minimize_core_partial;
        TRACE("sat", tout << "old core: " << s.get_core() << "\n";);
        literal_vector& core = get_core();
        literal_vector& mus = m_mus;
        if (core.size() > 64) {
            return mus2();
        }
        unsigned delta_time  = 0;
        unsigned core_miss = 0;
        while (!core.empty()) {
            IF_VERBOSE(3, verbose_stream() << "(opt.mus reducing core: " << core.size() << " mus: " << mus.size() << ")\n";);
            TRACE("sat", 
                  tout << "core: " << core << "\n";
                  tout << "mus:  " << mus  << "\n";);

            if (s.canceled()) {
                set_core();
                return l_undef;
            }
            if (minimize_partial && 3*delta_time > core.size() && core.size() < mus.size()) {
                break;
            }
            unsigned num_literals = core.size() + mus.size();
            if (num_literals <= 2) {
                // IF_VERBOSE(0, verbose_stream() << "num literals: " << core << " " << mus << "\n";);
                break;
            }
            if (s.m_config.m_minimize_core_partial && s.m_stats.m_restart - m_restart > m_max_restarts) {
                IF_VERBOSE(1, verbose_stream() << "restart budget exceeded\n";);
                set_core();
                return l_true;
            }

            literal lit = core.back();
            core.pop_back();
            lbool is_sat;
            {
                scoped_append _sa(mus, core);
                mus.push_back(~lit); 
                is_sat = s.check(mus.size(), mus.c_ptr());
                TRACE("sat", tout << "mus: " << mus << "\n";);
            }
            switch (is_sat) {
            case l_undef:
                core.push_back(lit);
                set_core();
                return l_undef;
            case l_true: {
                SASSERT(value_at(lit, s.get_model()) == l_false);
                mus.push_back(lit);
                update_model();
                if (!core.empty()) {
                    // mr(); // TBD: measure
                }
                break;
            }
            case l_false:
                literal_vector const& new_core = s.get_core();
                if (new_core.contains(~lit)) {
                    IF_VERBOSE(3, verbose_stream() << "miss core " << lit << "\n";);
                    ++core_miss;
                }
                else {
                    core_miss = 0;
                    TRACE("sat", tout << "core: " << new_core << " mus: " << mus << "\n";);
                    core.reset();
                    for (unsigned i = 0; i < new_core.size(); ++i) {
                        literal lit = new_core[i];
                        if (!mus.contains(lit)) {
                            core.push_back(lit);
                        }
                    }
                }
                break;
            }

            unsigned new_num_literals = core.size() + mus.size();
            if (new_num_literals == num_literals) {
                delta_time++;
            }
            else {
                delta_time = 0;
            }
        }
        set_core();
        IF_VERBOSE(3, verbose_stream() << "(sat.mus.new " << s.m_core << ")\n";);
        return l_true;
    }
    

    // bisection search.
    lbool mus::mus2() {
        literal_set core(get_core());
        literal_set support;
        lbool is_sat = qx(core, support, false);
        s.m_core.reset();
        s.m_core.append(core.to_vector());
        IF_VERBOSE(3, verbose_stream() << "(sat.mus.new " << s.m_core << ")\n";);
        return is_sat;
    }

    lbool mus::qx(literal_set& assignment, literal_set& support, bool has_support) {
        lbool is_sat = l_true;
        if (s.m_config.m_minimize_core_partial && s.m_stats.m_restart - m_restart > m_max_restarts) {
            IF_VERBOSE(1, verbose_stream() << "restart budget exceeded\n";);
            return l_true;
        }
        if (has_support) {
            scoped_append _sa(m_mus, support.to_vector());
            is_sat = s.check(m_mus.size(), m_mus.c_ptr());
            switch (is_sat) {
            case l_false: {
                literal_set core(s.get_core());
                support &= core;
                assignment.reset();
                return l_true;
            }
            case l_undef:
                return l_undef;
            case l_true:
                update_model();
                break;
            default:
                break;
            }
        }
        if (assignment.size() == 1) {
            return l_true;
        }
        literal_set assign2;
        split(assignment, assign2);
        support |= assignment;
        is_sat = qx(assign2, support, !assignment.empty());        
        unsplit(support, assignment);
        if (is_sat != l_true) return is_sat;
        support |= assign2;
        is_sat = qx(assignment, support, !assign2.empty());
        assignment |= assign2;
        unsplit(support, assign2);
        return is_sat;
    }

    void mus::unsplit(literal_set& A, literal_set& B) {
        literal_set A1, B1;
        literal_set::iterator it = A.begin(), end = A.end();
        for (; it != end; ++it) {
            if (B.contains(*it)) {
                B1.insert(*it);
            }
            else {
                A1.insert(*it);
            }
        }
        A = A1;
        B = B1;
    }

    void mus::split(literal_set& lits1, literal_set& lits2) {
        unsigned half = lits1.size()/2;
        literal_set lits3;
        literal_set::iterator it = lits1.begin(), end = lits1.end();
        for (unsigned i = 0; it != end; ++it, ++i) {
            if (i < half) {
                lits3.insert(*it);
            }
            else {
                lits2.insert(*it);
            }
        }
        lits1 = lits3;
    }

    literal_vector& mus::get_core() {
        m_core.reset();
        m_mus.reset();
        literal_vector& core = m_core;
        core.append(s.get_core());        
        for (unsigned i = 0; i < core.size(); ++i) {
            if (s.m_user_scope_literals.contains(core[i])) {
                m_mus.push_back(core[i]);
                core[i] = core.back();
                core.pop_back();
                --i;
            }
        }
        return core;
    }

    void mus::verify_core(literal_vector const& core) {
        lbool is_sat = s.check(core.size(), core.c_ptr());
        IF_VERBOSE(3, verbose_stream() << "core verification: " << is_sat << " " << core << "\n";);
    }

    void mus::mr() {
        sls sls(s);
        literal_vector tabu;
        tabu.append(m_mus);
        tabu.append(m_core);
        bool reuse_model = false;
        for (unsigned i = m_mus.size(); i < tabu.size(); ++i) {
            tabu[i] = ~tabu[i];
            lbool is_sat = sls(tabu.size(), tabu.c_ptr(), reuse_model); 
            tabu[i] = ~tabu[i];
            if (is_sat == l_true) {
                m_mus.push_back(tabu[i]);
                m_core.erase(tabu[i]);
                IF_VERBOSE(3, verbose_stream() << "in core " << tabu[i] << "\n";);
                reuse_model = true;
            }
            else {
                IF_VERBOSE(3, verbose_stream() << "NOT in core " << tabu[i] << "\n";);
                reuse_model = false;
            }
        }
    }
}

