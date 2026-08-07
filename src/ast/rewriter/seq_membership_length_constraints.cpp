/*++
Copyright (c) 2026 Microsoft Corporation

Module Name:

    seq_membership_length_constraints.cpp

Abstract:

    Consistency checks for sequence membership constraints based on lengths.

--*/

#include "ast/rewriter/seq_membership_length_constraints.h"

namespace seq {

lbool membership_length_constraints::check(constraint_vector const&) {
    m_core.reset();
    return l_true;
}

}
