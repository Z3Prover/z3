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
    bool            m_array_canonize_simplify = false;
    bool            m_array_simplify = true; // temporary hack for disabling array simplifier plugin.
    array_solver_id m_array_mode = array_solver_id::AR_FULL;
    bool            m_array_weak = false;
    bool            m_array_extensional = true;
    unsigned        m_array_laziness = 1;
    bool            m_array_delay_exp_axiom = true;
    bool            m_array_cg = false;
    bool            m_array_always_prop_upward = true;
    bool            m_array_lazy_ieq = false;
    unsigned        m_array_lazy_ieq_delay = 10;
    bool            m_array_fake_support = false;       // fake support for all array operations to pretend they are satisfiable.

    void updt_params(params_ref const & _p);

    void display(std::ostream & out) const;
};



