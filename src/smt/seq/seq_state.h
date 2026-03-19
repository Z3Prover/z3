/*++
Copyright (c) 2026 Microsoft Corporation

Module Name:

    seq_state.h

Abstract:

    Tracked constraint types bridging the SMT context to the Nielsen graph.
    tracked_str_eq and tracked_str_mem extend the core constraint types with
    SMT-layer source information (enodes and literals) for conflict reporting.

Author:

    Clemens Eisenhofer 2026-03-01
    Nikolaj Bjorner (nbjorner) 2026-03-01

--*/
#pragma once

#include "util/vector.h"
#include "smt/seq/seq_nielsen.h"
#include "util/sat_literal.h"

namespace smt {

    class enode;

    struct tracked_str_eq : public seq::str_eq {
        enode *m_l, *m_r;
        tracked_str_eq(euf::snode *lhs, euf::snode *rhs, smt::enode *l, smt::enode *r, seq::dep_tracker const &dep)
            : seq::str_eq(lhs, rhs, dep), m_l(l), m_r(r) {}
    };

    struct tracked_str_mem : public seq::str_mem {
        sat::literal lit;
        tracked_str_mem(euf::snode *str, euf::snode *regex, sat::literal lit, euf::snode *history, unsigned id, seq::dep_tracker const &dep)
            : seq::str_mem(str, regex, history, id, dep), lit(lit) {}
    };

}
