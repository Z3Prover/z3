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

#include "sat/sat_solver.h"
#include "sat/sat_mus.h"

namespace sat {

    mus::mus(solver& s):s(s), m_is_active(false), m_max_num_restarts(UINT_MAX) {}

    mus::~mus() {}
   
    void mus::reset() {
        m_core.reset();
        m_mus.reset();
        m_model.reset();
    }

    void mus::set_core() {   
        m_mus.append(m_core);
        s.m_core.reset();
        s.m_core.append(m_mus);
        TRACE("sat", tout << "new core: " << s.m_core << "\n";);
    }

    void mus::update_model() {
        if (m_model.empty()) {
            m_model.append(s.m_model);
        }
    }

    lbool mus::operator()() {
        m_max_num_restarts = s.m_config.m_core_minimize_partial ? s.num_restarts() + 10 : UINT_MAX;
        flet<bool> _disable_min(s.m_config.m_core_minimize, false);
        flet<bool> _is_active(m_is_active, true);
        IF_VERBOSE(3, verbose_stream() << "(sat.mus size: " << s.get_core().size() << " core: [" << s.get_core() << "])\n";);
        reset();
        lbool r = mus1();
        return r;
    }

    lbool mus::mus1() {
        bool minimize_partial = s.m_config.m_core_minimize_partial;
        TRACE("sat", tout << "old core: " << s.get_core() << "\n";);
        literal_vector& core = get_core();
        literal_vector& mus = m_mus;
        if (!minimize_partial && core.size() > 64) {
            return mus2();
        }
        while (!core.empty()) {
            IF_VERBOSE(1, verbose_stream() << "(sat.mus num-to-process: " << core.size() << " mus: " << mus.size();
                       if (minimize_partial) verbose_stream() << " max-restarts: " << m_max_num_restarts;
                       verbose_stream() << ")\n";);
            TRACE("sat", 
                  tout << "core: " << core << "\n";
                  tout << "mus:  " << mus  << "\n";);

            if (s.canceled()) {
                set_core();
                return l_undef;
            }
            unsigned num_literals = core.size() + mus.size();
            if (num_literals <= 2) {
                // IF_VERBOSE(0, verbose_stream() << "num literals: " << core << " " << mus << "\n";);
                break;
            }

            literal lit = core.back();
            core.pop_back();
            lbool is_sat;
            {
                flet<unsigned> _restart_bound(s.m_config.m_restart_max, m_max_num_restarts);
                scoped_append _sa(mus, core);
                mus.push_back(~lit); 
                is_sat = s.check(mus.size(), mus.data());
                TRACE("sat", tout << "mus: " << mus << "\n";);
            }
            IF_VERBOSE(1, verbose_stream() << "(sat.mus " << is_sat << ")\n";);
            switch (is_sat) {
            case l_undef:
                if (!s.canceled()) {
                    // treat restart max as sat, so literal is in the mus
                    mus.push_back(lit);
                }
                else {
                    core.push_back(lit);
                    set_core();
                    return l_undef;
                }
                break;
            case l_true: {
                SASSERT(value_at(lit, s.get_model()) == l_false);
                mus.push_back(lit);
                update_model();
                break;
            }
            case l_false:
                literal_vector const& new_core = s.get_core();
                if (new_core.contains(~lit)) {
                    IF_VERBOSE(3, verbose_stream() << "(sat.mus unit reduction, literal is in both cores " << lit << ")\n";);
                }
                else {
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
        if (has_support) {
            scoped_append _sa(m_mus, support.to_vector());
            is_sat = s.check(m_mus.size(), m_mus.data());            
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
        lbool is_sat = s.check(core.size(), core.data());
        IF_VERBOSE(3, verbose_stream() << "core verification: " << is_sat << " " << core << "\n";);
    }

}

