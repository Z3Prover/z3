/*++
Copyright (c) 2026 Microsoft Corporation

Module Name:

    seq_parikh.h

Abstract:

    Parikh-image filter over string equations and regex memberships.
    Refutation only: check() returns l_false with a core, or l_undef.

    Rule 1.  Flatten both sides of lhs = rhs into tokens: a string literal
    contributes one constant element per character, seq.unit of a value
    contributes that element, any other token is opaque and contributes
    itself.  If both sides carry the same multiset of opaque tokens then
    those cancel and the constant elements have to balance too.

        x."ab".y = y."ba".x    balanced          - no information
        x."a"    = "b".x       unbalanced        - unsatisfiable
        x."a"    = y."a"       opaque differ     - skipped

    Cancellation is by term identity, so no notion of "variable" is needed.

    Equations are handled one at a time; memberships are recorded but unused.

Author:

    Clemens Eisenhofer 2026

--*/
#pragma once

#include "ast/rewriter/seq_rewriter.h"
#include "util/lbool.h"
#include "util/obj_hashtable.h"
#include "util/statistics.h"
#include "util/trail.h"
#include <tuple>

class seq_parikh {

    struct stats {
        unsigned m_eqs_checked = 0;    // opaque tokens cancelled
        unsigned m_eqs_skipped = 0;    // opaque tokens did not cancel
        unsigned m_conflicts = 0;
    };

    // (lhs, rhs, dep) for equations, (term, regex, dep) for memberships
    using constraint_vec = vector<std::tuple<expr_ref, expr_ref, void*>>;

    ast_manager&     m;
    seq_rewriter&    m_rw;
    trail_stack&     m_undo_trail;
    expr_ref_vector  m_pin;         // pins the constant elements the count maps key on
    constraint_vec   m_eqs;
    constraint_vec   m_mems;
    ptr_vector<void> m_core;
    stats            m_stats;
    lbool            m_last_result = l_undef;

    seq_util& u() const { return m_rw.u(); }

    // Signed token counts of one side, +1 for the left and -1 for the right one.
    void count_tokens(expr* t, int sign, obj_map<expr, int>& elems, obj_map<expr, int>& opaque);

public:
    seq_parikh(seq_rewriter& rw, trail_stack& undo_trail) :
        m(rw.m()), m_rw(rw), m_undo_trail(undo_trail), m_pin(rw.m()) {}

    void collect_statistics(::statistics& st) const;

    std::ostream& display(std::ostream& out) const;

    // Assert lhs = rhs for the next check().  The dependency d is used for core
    // tracking and may be nullptr.  Retracted when the trail is popped.
    void add_eq(expr* lhs, expr* rhs, void* d);

    // Assert term in regex.  Recorded for later rules, ignored by check().
    void add_mem(expr* term, expr* regex, void* d);

    // Refute a single equation on its own, leaving the asserted ones untouched.
    lbool check_eq(expr* lhs, expr* rhs);

    // l_false as soon as one asserted equation is refuted, l_undef when none is.
    lbool check();

    // Dependency of the equation refuted by the last check(), if it had one.
    ptr_vector<void> const& core() const { return m_core; }
};
