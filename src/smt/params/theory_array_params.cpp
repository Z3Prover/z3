/*++
Copyright (c) 2006 Microsoft Corporation

Module Name:

    theory_array_params.cpp

Abstract:

    <abstract>

Author:

    Leonardo de Moura (leonardo) 2008-05-06.

Revision History:

--*/
#include "smt/params/theory_array_params.h"
#include "smt/params/smt_params_helper.hpp"

void theory_array_params::updt_params(params_ref const & _p) {
    smt_params_helper p(_p);
    m_array_weak = p.array_weak();
    m_array_extensional = p.array_extensional();
}

#define DISPLAY_PARAM(X) out << #X"=" << X << std::endl;

void theory_array_params::display(std::ostream & out) const {
    DISPLAY_PARAM(m_array_mode);
    DISPLAY_PARAM(m_array_weak);
    DISPLAY_PARAM(m_array_extensional);
    DISPLAY_PARAM(m_array_laziness);
    DISPLAY_PARAM(m_array_delay_exp_axiom);
    DISPLAY_PARAM(m_array_cg);
    DISPLAY_PARAM(m_array_always_prop_upward);
    DISPLAY_PARAM(m_array_lazy_ieq);
    DISPLAY_PARAM(m_array_lazy_ieq_delay);
}
