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

    without leaving m_region.

    Views on the same value are conjunctive: the admissible values are the
    intersection of their languages.  See seq_monadic, which reports the
    decomposition it commits to as views.

Author:

    Clemens Eisenhofer 2026

--*/
#pragma once

#include "ast/ast.h"
#include "ast/rewriter/seq_rewriter.h"
#include "util/lbool.h"
#include "util/uint_set.h"
#include "util/vector.h"

namespace seq {

    struct view {
        expr*           m_state = nullptr;
        expr*           m_target = nullptr;     // null: membership view
        uint_set const* m_region = nullptr;     // null: whole automaton

        // identity for dedup/memoization; covers the same fields as operator==
        struct sig {
            unsigned        state, target;
            uint_set const* region;
        };

        view() = default;
        view(expr* state, expr* target, uint_set const* region = nullptr) :
            m_state(state), m_target(target), m_region(region) {}

        static view membership(expr* state, uint_set const* region = nullptr) {
            return view(state, nullptr, region);
        }

        static view reach(expr* state, expr* target, uint_set const* region = nullptr) {
            return view(state, target, region);
        }

        bool is_membership() const { return m_target == nullptr; }
        bool is_reach() const { return m_target != nullptr; }

        bool in_region() const {
            return !m_region || (m_state && m_region->contains(m_state->get_id()));
        }

        sig key() const {
            return { m_state ? m_state->get_id() : UINT_MAX,
                     m_target ? m_target->get_id() : UINT_MAX,
                     m_region };
        }

        bool operator==(view const& other) const {
            return m_state == other.m_state && m_target == other.m_target
                && m_region == other.m_region;
        }

        bool operator!=(view const& other) const { return !(*this == other); }
    };

    inline bool operator<(view::sig const& a, view::sig const& b) {
        if (a.state != b.state) return a.state < b.state;
        if (a.target != b.target) return a.target < b.target;
        return a.region < b.region;
    }

    inline bool operator==(view::sig const& a, view::sig const& b) {
        return a.state == b.state && a.target == b.target
            && a.region == b.region;
    }

    using view_vector = svector<view>;

    // Uncached reference semantics; an engine with its own caches has to agree with these.
    // l_undef when nullability is undecided.
    lbool accepts(view const& v, seq_rewriter& rw);

    // Empty language.
    bool is_dead(view const& v, seq_rewriter& rw);

}
