/*++
Copyright (c) 2026 Microsoft Corporation

Module Name:

    seq_view.cpp

Abstract:

    Reference semantics for seq::view (see seq_view.h).  Uncached, so that a client
    can evaluate a view without owning an engine.

Author:

    Clemens Eisenhofer 2026

--*/

#include "ast/rewriter/seq_view.h"

namespace seq {

    lbool accepts(view const& v, seq_rewriter& rw) {
        lbool r;
        if (!v.m_state || !v.in_region())
            r = l_false;
        else if (v.is_reach())
            r = v.m_state == v.m_target ? l_true : l_false;
        else {
            expr_ref nb = rw.is_nullable(v.m_state);
            ast_manager& m = rw.m();
            r = m.is_true(nb) ? l_true : m.is_false(nb) ? l_false : l_undef;
        }
        return r;
    }

    bool is_dead(view const& v, seq_rewriter& rw) {
        return !v.m_state || !v.in_region() || rw.u().re.is_empty(v.m_state);
    }

}
