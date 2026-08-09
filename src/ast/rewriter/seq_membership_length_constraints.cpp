/*++
Copyright (c) 2026 Microsoft Corporation

Module Name:

    seq_membership_length_constraints.cpp

Abstract:

    Consistency checks for sequence membership constraints based on lengths.

--*/

#include "ast/rewriter/seq_membership_length_constraints.h"
#include "ast/rewriter/seq_rewriter.h"

namespace seq {

lbool membership_length_constraints::check(constraint_vector const& constraints) {
    m_core.reset();
    for (auto const& [term, regex, dependency] : constraints) {
        unsigned min_length = m_rw.u().str.min_length(term);
        unsigned max_length = m_rw.u().re.max_length(regex);
        if (min_length <= max_length)
            continue;
        if (dependency)
            m_core.push_back(dependency);
        return l_false;
    }
    return l_true;
}

}
