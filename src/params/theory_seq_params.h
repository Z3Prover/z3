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
    bool m_split_w_len = false;
    bool m_seq_validate = false;
    bool m_seq_regex_monadic = false;
    unsigned m_seq_regex_budget = 1000000;
    unsigned m_seq_regex_split = 0;
    symbol m_seq_regex_transition_mode = symbol("light-ant");
    symbol m_seq_regex_orientation = symbol("forward");
    unsigned m_seq_max_unfolding = UINT_MAX/4;
    unsigned m_seq_min_unfolding = 1;

    theory_seq_params(params_ref const & p = params_ref()) {
        updt_params(p);
    }

    void updt_params(params_ref const & p);
};
