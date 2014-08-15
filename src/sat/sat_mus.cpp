/*++
Copyright (c) 2014 Microsoft Corporation

Module Name:

    sat_mus.cpp

Abstract:
   
    Faster MUS extraction based on Belov et.al. HYB (Algorithm 3, 4)

Author:

    Nikolaj Bjorner (nbjorner) 2014-20-7

Notes:


--*/

#include "sat_solver.h"
#include "sat_mus.h"
#include "sat_sls.h"

namespace sat {

    mus::mus(solver& s):s(s) {}

    mus::~mus() {}
   
    void mus::reset() {
        m_core.reset();
        m_mus.reset();
    }

    void mus::set_core() {        
        m_core.append(m_mus);                
        s.m_core.reset();
        s.m_core.append(m_core);
    }

    lbool mus::operator()() {
        flet<bool> _disable_min(s.m_config.m_minimize_core, false);
        flet<bool> _disable_opt(s.m_config.m_optimize_model, false);
        TRACE("sat", tout << "old core: " << s.get_core() << "\n";);
        IF_VERBOSE(2, verbose_stream() << "(sat.mus " << s.get_core() << ")\n";);
        reset();
        literal_vector& core = m_core;
        literal_vector& mus = m_mus;
        core.append(s.get_core());        
        for (unsigned i = 0; i < core.size(); ++i) {
            s.m_user_scope_literals.contains(core[i]);
            mus.push_back(core[i]);
            core[i] = core.back();
            core.pop_back();
            --i;
        }

        while (!core.empty()) {
            TRACE("sat", 
                  tout << "core: " << core << "\n";
                  tout << "mus:  " << mus  << "\n";);

            if (s.m_cancel) {
                set_core();
                return l_undef;
            }
            literal lit = core.back();
            core.pop_back();
            unsigned sz = mus.size();
            // mus.push_back(~lit); // TBD: measure
            mus.append(core);
            lbool is_sat = s.check(mus.size(), mus.c_ptr());
            TRACE("sat", tout << "mus: " << mus << "\n";);
            mus.resize(sz);
            switch (is_sat) {
            case l_undef:
                core.push_back(lit);
                set_core();
                return l_undef;
            case l_true: {
                SASSERT(value_at(lit, s.get_model()) == l_false);
                mus.push_back(lit);
                if (!core.empty()) {
                    // mr(); // TBD: measure
                }
                break;
            }
            case l_false:
                literal_vector const& new_core = s.get_core();
                if (new_core.contains(~lit)) {
                    break;
                }
                TRACE("sat", tout << "new core: " << new_core << "\n";);
                core.reset();
                for (unsigned i = 0; i < new_core.size(); ++i) {
                    literal lit = new_core[i];
                    if (!mus.contains(lit)) {
                        core.push_back(lit);
                    }
                }
                break;
            }
        }
        TRACE("sat", tout << "new core: " << mus << "\n";);
        set_core();
        IF_VERBOSE(2, verbose_stream() << "(sat.mus.new " << core << ")\n";);
        return l_true;
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
                IF_VERBOSE(2, verbose_stream() << "in core " << tabu[i] << "\n";);
                reuse_model = true;
            }
            else {
                IF_VERBOSE(2, verbose_stream() << "NOT in core " << tabu[i] << "\n";);
                reuse_model = false;
            }
        }
    }
}

