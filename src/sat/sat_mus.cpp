/*++
Copyright (c) 2014 Microsoft Corporation

Module Name:

    sat_mus.cpp

Abstract:
   
    Faster MUS extraction based on Belov et.al. HYB (Algorithm 3, 4)

Author:

    Nikolaj Bjorner (nbjorner) 2014-20-7

Notes:

   Model rotation needs fixes to ensure that hard constraints are satisfied
   under pertubed model. Model rotation also has o be consistent with theories.

--*/

#include "sat_solver.h"
#include "sat_mus.h"

namespace sat {

    mus::mus(solver& s):s(s) {}

    mus::~mus() {}
   
    void mus::reset() {
        m_core.reset();
        m_mus.reset();
        m_assumptions.reset();
    }

    void mus::set_core() {
        m_core.append(m_mus);                
        s.m_core.reset();
        s.m_core.append(m_core);
    }

    lbool mus::operator()() {
        reset();
        literal_vector& core = m_core;
        literal_vector& mus = m_mus;
        literal_vector& assumptions = m_assumptions;
        core.append(s.get_core());
        SASSERT(!core.empty());

        if (core.size() == 1) {
            return l_true;
        }
        while (!core.empty()) {
            TRACE("sat", 
                  tout << "core: " << core << "\n";
                  tout << "mus:  " << mus << "\n";);

            if (s.m_cancel) {
                set_core();
                return l_undef;
            }
            literal lit = core.back();
            core.pop_back();
            unsigned sz = assumptions.size();
            assumptions.push_back(~lit);
            assumptions.append(core);
            lbool is_sat = s.check(assumptions.size(), assumptions.c_ptr());
            assumptions.resize(sz);
            switch (is_sat) {
            case l_undef:
                core.push_back(lit);
                set_core();
                return l_undef;
            case l_true: {
                assumptions.push_back(lit);
                mus.push_back(lit);
                unsigned sz = core.size();
                core.append(mus);
                rmr();
                core.resize(sz);
                break;
            }
            case l_false:
                core.reset();
                for (unsigned i = 0; i < s.get_core().size(); ++i) {
                    literal lit = s.get_core()[i];
                    if (!mus.contains(lit)) {
                        core.push_back(lit);
                    }
                }
                break;
            }
        }
        return l_true;
    }

    lbool mus::eval(literal l) const {
        return value_at(l, s.get_model());
    }

    void mus::rmr() {
        model& model = s.m_model;
        literal lit = m_mus.back();
        literal assumption_lit;
        SASSERT(eval(lit) == l_false); // literal is false in current model.
        find_swappable(lit);
        for (unsigned i = 0; i < m_toswap.size(); ++i) {
            lit = m_toswap[i];
            SASSERT(eval(lit) == l_false);  
            model[lit.var()] = ~model[lit.var()];    // swap assignment
            if (has_single_unsat(assumption_lit) && !m_mus.contains(assumption_lit)) {
                m_mus.push_back(assumption_lit);
                rmr();
            }
            model[lit.var()] = ~model[lit.var()];    // swap assignment back            
        }
    }

    bool mus::has_single_unsat(literal& assumption_lit) {
        model const& model = s.get_model();
        return false;
    }

    void mus::find_swappable(literal lit) {
        m_toswap.reset();
    }

}

#if 0


    bool has_single_unsat(svector<bool> const& model, unsigned& cls_id) const {
        cls_id = UINT_MAX;
        for (unsigned i = 0; i < m_cls2lits.size(); ++i) {
            if (!eval(model, m_cls2lits[i])) {
                if (cls_id == UINT_MAX) {
                    cls_id = i;
                }
                else {
                    return false;
                }
            }
        }
        TRACE("opt", display_vec(tout << "clause: " << cls_id << " model: ", model););
        return cls_id != UINT_MAX;
    }

    bool eval(svector<bool> const& model, smt::literal_vector const& cls) const {
        bool result = false;
        for (unsigned i = 0; !result && i < cls.size(); ++i) {
            result = (model[cls[i].var()] != cls[i].sign());
        }
        TRACE("opt", display_vec(tout << "model: ", model);
              display_vec(tout << "clause: ", cls);
              tout << "result: " << result << "\n";);
        return result;
    }


#endif
