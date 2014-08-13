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
        m_model.reset();
    }

    lbool mus::operator()() {
        flet<bool> _disable_min(s.m_config.m_minimize_core, false);
        TRACE("sat", tout << "old core: " << s.get_core() << "\n";);
        IF_VERBOSE(2, verbose_stream() << "(sat.mus " << s.get_core() << ")\n";);
        reset();
        literal_vector& core = m_core;
        literal_vector& mus = m_mus;
        core.append(s.get_core());
        

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
            mus.push_back(~lit); // TBD: measure
            mus.append(core);
            lbool is_sat = s.check(mus.size(), mus.c_ptr());
            mus.resize(sz);
            switch (is_sat) {
            case l_undef:
                core.push_back(lit);
                set_core();
                return l_undef;
            case l_true: {
                SASSERT(value_at(lit, s.get_model()) == l_false);
                mus.push_back(lit);
                if (core.empty()) {
                    break;
                }
                sz = core.size();
                core.append(mus);
                measure_mr();
                // rmr();
                core.resize(sz);
                break;
            }
            case l_false:
                literal_vector const& new_core = s.get_core();
                if (new_core.contains(~lit)) {
                    break;
                }
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

    void mus::measure_mr() {
        model const& m2 = s.get_model();
        if (!m_model.empty()) {
            unsigned n = 0;
            for (unsigned i = 0; i < m_model.size(); ++i) {
                if (m2[i] != m_model[i]) ++n;
            }
            std::cout << "model diff: " << n << " out of " << m_model.size() << "\n";
        }
        m_model.reset();
        m_model.append(m2);        
    }

    // 
    // TBD: eager model rotation allows rotating the same clause 
    // several times with respect to different models.
    // 
    void mus::rmr() {
        return;
#if 0
        model& model = s.m_model;
        literal lit = m_mus.back();
        literal assumption_lit;
        SASSERT(value_at(lit, model) == l_false); 
        // literal is false in current model.
        unsigned sz = m_toswap.size();
        find_swappable(lit);
        unsigned sz1 = m_toswap.size();
        for (unsigned i = sz; i < sz1; ++i) {
            lit = m_toswap[i];
            SASSERT(value_at(lit, model) == l_false);  
            model[lit.var()] = ~model[lit.var()];    // swap assignment
            if (has_single_unsat(assumption_lit) && !m_mus.contains(assumption_lit)) {
                m_mus.push_back(assumption_lit);
                rmr();
            }
            model[lit.var()] = ~model[lit.var()];    // swap assignment back            
        }
        m_toswap.resize(sz);
#endif
    }

    bool mus::has_single_unsat(literal& assumption_lit) {
        model const& model = s.get_model();
        return false;
    }

    //
    // lit is false in model.
    // find clauses where ~lit occurs, and all other literals
    // are false in model.
    // for each of the probed literals, determine if swapping the
    // assignment falsifies a hard clause, if not, add to m_toswap.
    // 

    void mus::find_swappable(literal lit) {
        IF_VERBOSE(3, verbose_stream() << "(sat.mus swap " << lit << ")\n";);
        unsigned sz = m_toswap.size();
        literal lit2, lit3;
        model const& model = s.get_model();
        SASSERT(value_at(lit, model) == l_false);  
        watch_list const& wlist = s.get_wlist(lit);
        watch_list::const_iterator it  = wlist.begin();
        watch_list::const_iterator end = wlist.end();
        unsigned num_cand = 0;
        for (; it != end && num_cand <= 1; ++it) {
            switch (it->get_kind()) {
            case watched::BINARY:
                if (it->is_learned()) {
                    break;
                }
                lit2 = it->get_literal();
                if (value_at(lit2, model) == l_true) {
                    break;
                }
                IF_VERBOSE(1, verbose_stream() << "(" << ~lit << " " << lit2 << ") ";);
                TRACE("sat", tout << ~lit << " " << lit2 << "\n";);
                ++num_cand;
                break;
            case watched::TERNARY:
                lit2 = it->get_literal1();
                lit3 = it->get_literal2();
                if (value_at(lit2, model) == l_true) {
                    break;
                }
                if (value_at(lit3, model) == l_true) {
                    break;
                }

                IF_VERBOSE(1, verbose_stream() << "(" << ~lit << " " << lit2 << " " << lit3 << ") ";);
                ++num_cand;
                break;
            case watched::CLAUSE: {
                clause_offset cls_off = it->get_clause_offset();
                clause& c = *(s.m_cls_allocator.get_clause(cls_off));
                if (c.is_learned()) {
                    break;
                }
                ++num_cand;
                IF_VERBOSE(1, verbose_stream() << c << " ";);
                TRACE("sat", tout << c << "\n";);
                break;
            }
            case watched::EXT_CONSTRAINT:
                TRACE("sat", tout << "external constraint - should avoid rmr\n";);
                return;
            }
        }
        if (num_cand > 1) {
            m_toswap.resize(sz);
        }
        else {
            IF_VERBOSE(1, verbose_stream() << "wlist size: " << num_cand << " " << m_core.size() << "\n";);
        }

    }

}

