/*++
Copyright (c) 2013 Microsoft Corporation

Module Name:

    theory_pb_params.h

Abstract:

    <abstract>

Author:

    Nikolaj Bjorner (nbjorner) 2014-01-01

Revision History:

--*/
#pragma once

#include "util/params.h"


struct theory_pb_params {
    unsigned m_pb_conflict_frequency = 1000;
    bool     m_pb_learn_complements = true;
    theory_pb_params(params_ref const & p = params_ref()) {
        updt_params(p);
    }
    
    void updt_params(params_ref const & p);

    void display(std::ostream & out) const;
};


