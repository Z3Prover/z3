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

    A GATED reach view additionally requires every state of the run to lie in m_gate
    (the view nu_Q^{target}(state) of the landing decomposition, see seq_deriv_graph).
    Gates are only built over Brzozowski states.

Author:

    Clemens Eisenhofer 2026

--*/
#pragma once

#include "ast/ast.h"
#include "ast/rewriter/seq_rewriter.h"
#include "util/lbool.h"
#include "util/vector.h"
#include <algorithm>

namespace seq {

    // A frozen set of derivative states, owned by a seq::deriv_graph.
    struct region {
        unsigned          m_id;
        unsigned_vector   m_ids;        // sorted expression ids
        ptr_vector<expr>  m_states;
        bool contains(expr* e) const { return std::binary_search(m_ids.begin(), m_ids.end(), e->get_id()); }
    };

    struct view {
        expr_ref        m_state;
        expr_ref        m_target;     // null: membership view
        region const*   m_gate = nullptr;

        // identity for dedup/memoization; covers the same fields as operator==
        struct sig {
            unsigned        state, target, gate;
        };

        view(ast_manager& m) : m_state(m), m_target(m) {}
        view(expr* state, expr* target, ast_manager& m) :
            m_state(state, m), m_target(target, m) {}
        view(expr* state, expr* target, region const* gate, ast_manager& m) :
            m_state(state, m), m_target(target, m), m_gate(gate) {}

        static view membership(expr* state, ast_manager& m) {
            return view(state, nullptr, m);
        }

        static view reach(expr* state, expr* target, ast_manager& m) {
            return view(state, target, m);
        }

        static view gated(expr* state, expr* target, region const* gate, ast_manager& m) {
            return view(state, target, gate, m);
        }

        bool is_membership() const { return m_target.get() == nullptr; }
        bool is_reach() const { return m_target.get() != nullptr; }
        bool is_gated() const { return m_gate != nullptr; }

        sig key() const {
            return { m_state ? m_state->get_id() : UINT_MAX,
                     m_target ? m_target->get_id() : UINT_MAX,
                     m_gate ? m_gate->m_id : UINT_MAX };
        }

        bool operator==(view const& other) const {
            return m_state.get() == other.m_state.get() && m_target.get() == other.m_target.get() && m_gate == other.m_gate;
        }

        bool operator!=(view const& other) const { return !(*this == other); }
    };

    inline bool operator<(view::sig const& a, view::sig const& b) {
        if (a.state != b.state) return a.state < b.state;
        if (a.target != b.target) return a.target < b.target;
        return a.gate < b.gate;
    }

    inline bool operator==(view::sig const& a, view::sig const& b) {
        return a.state == b.state && a.target == b.target && a.gate == b.gate;
    }

    using view_vector = vector<view>;

    // Uncached reference semantics; an engine with its own caches has to agree with these.
    // l_undef when nullability is undecided.
    lbool accepts(view const& v, seq_rewriter& rw);

    // Empty language: no value satisfies the view.
    bool is_dead(view const& v, seq_rewriter& rw);

}
