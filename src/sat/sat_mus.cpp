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

    mus::mus(solver& s):s(s), m_is_active(false) {}

    mus::~mus() {}
   
    void mus::reset() {
        m_core.reset();
        m_mus.reset();
        m_model.reset();
        m_best_value = 0;
    }

    void mus::set_core() {        
        m_core.append(m_mus);                
        s.m_core.reset();
        s.m_core.append(m_core);
    }

    lbool mus::operator()() {
        bool minimize_partial = s.m_config.m_minimize_core_partial;
        flet<bool> _disable_min(s.m_config.m_minimize_core, false);
        flet<bool> _disable_min_partial(s.m_config.m_minimize_core_partial, false);
        flet<bool> _disable_opt(s.m_config.m_optimize_model, false);
        flet<bool> _is_active(m_is_active, true);
        TRACE("sat", tout << "old core: " << s.get_core() << "\n";);
        IF_VERBOSE(2, verbose_stream() << "(sat.mus " << s.get_core() << ")\n";);
        reset();
        literal_vector& core = m_core;
        literal_vector& mus = m_mus;
        core.append(s.get_core());        
        for (unsigned i = 0; i < core.size(); ++i) {
            if (s.m_user_scope_literals.contains(core[i])) {
                mus.push_back(core[i]);
                core[i] = core.back();
                core.pop_back();
                --i;
            }
        }
        unsigned delta_time  = 0;
        while (!core.empty()) {
            IF_VERBOSE(2, verbose_stream() << "(opt.mus reducing core: " << core.size() << " new core: " << mus.size() << ")\n";);
            TRACE("sat", 
                  tout << "core: " << core << "\n";
                  tout << "mus:  " << mus  << "\n";);

            if (s.m_cancel) {
                set_core();
                return l_undef;
            }
            if (minimize_partial && delta_time > 4) {
                break;
            }
            unsigned num_literals = core.size() + mus.size();

            literal lit = core.back();
            core.pop_back();
            unsigned sz = mus.size();
            mus.append(core);
            mus.push_back(~lit); // TBD: measure
            lbool is_sat = s.check(mus.size(), mus.c_ptr());
            TRACE("sat", tout << "mus: " << mus << "\n";);
            switch (is_sat) {
            case l_undef:
                mus.resize(sz);
                core.push_back(lit);
                set_core();
                return l_undef;
            case l_true: {
                SASSERT(value_at(lit, s.get_model()) == l_false);
                mus.resize(sz);
                mus.push_back(lit);
                if (!core.empty()) {
                    // mr(); // TBD: measure
                }
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
                break;
            }
            case l_false:
                literal_vector const& new_core = s.get_core();
                if (new_core.contains(~lit)) {
                    mus.resize(sz);
                    break;
                }
                mus.resize(sz);
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

            unsigned new_num_literals = core.size() + mus.size();
            if (new_num_literals == num_literals) {
                delta_time++;
            }
            else {
                delta_time = 0;
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

