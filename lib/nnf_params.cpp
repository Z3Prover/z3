/*++
Copyright (c) 2006 Microsoft Corporation

Module Name:

    nnf_params.cpp

Abstract:

    <abstract>

Author:

    Leonardo de Moura (leonardo) 2008-01-14.

Revision History:

--*/
#include"nnf_params.h"

void nnf_params::register_params(ini_params & p) {
    p.register_unsigned_param("NNF_FACTOR", m_nnf_factor, "the maximum growth factor during NNF translation (auxiliary definitions are introduced if the threshold is reached)");
    p.register_int_param("NNF_MODE", 0, 3, reinterpret_cast<int&>(m_nnf_mode), "NNF translation mode: 0 - skolem normal form, 1 - 0 + quantifiers in NNF, 2 - 1 + opportunistic, 3 - full");
    p.register_bool_param("NNF_IGNORE_LABELS", m_nnf_ignore_labels, "remove/ignore labels in the input formula, this option is ignored if proofs are enabled");
    p.register_bool_param("NNF_SK_HACK", m_nnf_sk_hack, "hack for VCC");
}
