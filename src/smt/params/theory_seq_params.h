/*++
Copyright (c) 2018 Microsoft Corporation

Module Name:

    theory_seq_params.h

Abstract:

    Parameters for sequence theory plugin

Revision History:


--*/

#pragma once

#include "util/params.h"

struct theory_seq_params {
    /*
     * Enable splitting guided by length constraints
     */
    bool m_split_w_len;
    bool m_seq_validate;


    theory_seq_params(params_ref const & p = params_ref()):
        m_split_w_len(false),
        m_seq_validate(false)
    {
        updt_params(p);
    }

    void updt_params(params_ref const & p);
};

