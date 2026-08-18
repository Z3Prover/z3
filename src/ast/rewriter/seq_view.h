/*++
Copyright (c) 2026 Microsoft Corporation

Module Name:

    seq_view.h

Abstract:

    A view: a constraint on one sequence value, stated against a derivative
    automaton instead of as a concrete word.  Reading the value drives the
    automaton from m_state; the view holds when

        m_target ? the run ends at m_target      (reach view)
                 : the end state is nullable     (membership view)

    Views on the same value are conjunctive: the admissible values are the
    intersection of their languages.  See seq_monadic, which reports the
    decomposition it commits to as views.

    A REACH view is relative to a transition relation, and therefore to the
    seq::transition_mode of the engine that produced it: under light_antimirov_tm a
    derivative is split over its top-level unions, so reaching m_target means SOME run
    ends there, whereas under brzozowski_tm the derivative is a single state and the
    run is the deterministic one.  A client that evaluates views with the producing
    engine (product_nonempty, materialize) never sees the difference; a client that
    re-states them against an automaton of its own must build the engine in the mode
    that automaton steps in.  A MEMBERSHIP view is mode-independent: m_state denotes a
    language either way.

Author:

    Clemens Eisenhofer 2026

--*/
#pragma once

#include "ast/ast.h"
#include "ast/rewriter/seq_rewriter.h"
#include "util/lbool.h"
#include "util/vector.h"

namespace seq {

    struct view {
        expr*           m_state = nullptr;
        expr*           m_target = nullptr;     // null: membership view

        // identity for dedup/memoization; covers the same fields as operator==
        struct sig {
            unsigned        state, target;
        };

        view() = default;
        view(expr* state, expr* target) :
            m_state(state), m_target(target) {}

        static view membership(expr* state) {
            return view(state, nullptr);
        }

        static view reach(expr* state, expr* target) {
            return view(state, target);
        }

        bool is_membership() const { return m_target == nullptr; }
        bool is_reach() const { return m_target != nullptr; }

        sig key() const {
            return { m_state ? m_state->get_id() : UINT_MAX,
                     m_target ? m_target->get_id() : UINT_MAX };
        }

        bool operator==(view const& other) const {
            return m_state == other.m_state && m_target == other.m_target;
        }

        bool operator!=(view const& other) const { return !(*this == other); }
    };

    inline bool operator<(view::sig const& a, view::sig const& b) {
        if (a.state != b.state) return a.state < b.state;
        return a.target < b.target;
    }

    inline bool operator==(view::sig const& a, view::sig const& b) {
        return a.state == b.state && a.target == b.target;
    }

    using view_vector = svector<view>;

    // Uncached reference semantics; an engine with its own caches has to agree with these.
    // l_undef when nullability is undecided.
    lbool accepts(view const& v, seq_rewriter& rw);

    // Empty language: no value satisfies the view.
    bool is_dead(view const& v, seq_rewriter& rw);

}
