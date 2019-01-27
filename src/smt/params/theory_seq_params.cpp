/*++
Copyright (c) 2018 Microsoft Corporation

Module Name:

    theory_seq_params.cpp

Abstract:

    Parameters for sequence theory plugin

Revision History:


--*/

#include "smt/params/theory_seq_params.h"
#include "smt/params/smt_params_helper.hpp"

void theory_seq_params::updt_params(params_ref const & _p) {
    smt_params_helper p(_p);
    m_split_w_len = p.seq_split_w_len();
}
