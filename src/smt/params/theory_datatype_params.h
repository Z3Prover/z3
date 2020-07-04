/*++
Copyright (c) 2006 Microsoft Corporation

Module Name:

    theory_datatype_params.h

Abstract:

    <abstract>

Author:

    Leonardo de Moura (leonardo) 2008-11-04.

Revision History:

--*/
#pragma once

#include "smt/params/smt_params_helper.hpp"

struct theory_datatype_params {
    unsigned   m_dt_lazy_splits;

    theory_datatype_params():
        m_dt_lazy_splits(1) {
    }

    void updt_params(params_ref const & _p) {
        smt_params_helper p(_p);
        m_dt_lazy_splits = p.dt_lazy_splits(); 
    }

    void display(std::ostream & out) const { out << "m_dt_lazy_splits=" << m_dt_lazy_splits << std::endl; }
};



