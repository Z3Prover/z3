/*++
Copyright (c) 2006 Microsoft Corporation

Module Name:

    theory_array_params.h

Abstract:

    <abstract>

Author:

    Leonardo de Moura (leonardo) 2008-06-01.

Revision History:

--*/
#ifndef _THEORY_ARRAY_PARAMS_H_
#define _THEORY_ARRAY_PARAMS_H_

#include"array_simplifier_params.h"

enum array_solver_id {
    AR_NO_ARRAY,
    AR_SIMPLE,
    AR_MODEL_BASED,
    AR_FULL
};

struct theory_array_params : public array_simplifier_params {
    array_solver_id m_array_mode;
    bool            m_array_weak;
    bool            m_array_extensional;
    unsigned        m_array_laziness;
    bool            m_array_delay_exp_axiom;
    bool            m_array_cg;
    bool            m_array_always_prop_upward;
    bool            m_array_lazy_ieq;
    unsigned        m_array_lazy_ieq_delay;

    theory_array_params():
        m_array_mode(AR_FULL),
        m_array_weak(false),
        m_array_extensional(true),
        m_array_laziness(1),
        m_array_delay_exp_axiom(true),
        m_array_cg(false),
        m_array_always_prop_upward(true), // UPWARDs filter is broken... TODO: fix it
        m_array_lazy_ieq(false),
        m_array_lazy_ieq_delay(10) {
    }


    void updt_params(params_ref const & _p);

#if 0
    void register_params(ini_params & p) {
        p.register_int_param("array_solver", 0, 3, reinterpret_cast<int&>(m_array_mode), "0 - no array, 1 - simple, 2 - model based, 3 - full");
        p.register_bool_param("array_weak", m_array_weak);
        p.register_bool_param("array_extensional", m_array_extensional);
        p.register_unsigned_param("array_laziness", m_array_laziness);
        p.register_bool_param("array_delay_exp_axiom", m_array_delay_exp_axiom);
        p.register_bool_param("array_cg", m_array_cg);
        p.register_bool_param("array_always_prop_upward", m_array_always_prop_upward, 
                              "Disable the built-in filter upwards propagation");
        p.register_bool_param("array_lazy_ieq", m_array_lazy_ieq);
        p.register_unsigned_param("array_lazy_ieq_delay", m_array_lazy_ieq_delay);
        p.register_bool_param("array_canonize", m_array_canonize_simplify, 
                              "Normalize arrays into normal form during simplification");
    }
#endif

};


#endif /* _THEORY_ARRAY_PARAMS_H_ */

