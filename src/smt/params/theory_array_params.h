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
#pragma once

#include "util/params.h"

enum array_solver_id {
    AR_NO_ARRAY,
    AR_SIMPLE,
    AR_MODEL_BASED,
    AR_FULL
};

struct theory_array_params {
    bool            m_array_canonize_simplify;
    bool            m_array_simplify; // temporary hack for disabling array simplifier plugin.
    array_solver_id m_array_mode;
    bool            m_array_weak;
    bool            m_array_extensional;
    unsigned        m_array_laziness;
    bool            m_array_delay_exp_axiom;
    bool            m_array_cg;
    bool            m_array_always_prop_upward;
    bool            m_array_lazy_ieq;
    unsigned        m_array_lazy_ieq_delay;
    bool            m_array_fake_support;       // fake support for all array operations to pretend they are satisfiable.

    theory_array_params():
        m_array_canonize_simplify(false),
        m_array_simplify(true),
        m_array_mode(array_solver_id::AR_FULL),
        m_array_weak(false),
        m_array_extensional(true),
        m_array_laziness(1),
        m_array_delay_exp_axiom(true),
        m_array_cg(false),
        m_array_always_prop_upward(true), // UPWARDs filter is broken... TODO: fix it
        m_array_lazy_ieq(false),
        m_array_lazy_ieq_delay(10),
        m_array_fake_support(false) {
    }


    void updt_params(params_ref const & _p);

    void display(std::ostream & out) const;
};



