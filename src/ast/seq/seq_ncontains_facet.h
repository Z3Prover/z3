/*++
Copyright (c) 2026 Microsoft Corporation

Module Name:

    seq_ncontains_facet.h

Abstract:

    Negative `str.contains` facet.

    Positive `str.contains(h,n)` is reduced elsewhere to an equation
    `h = x.n.y`. This facet handles only the negative form
    `not contains(h,n)`.

    `ncontains_facet` owns pending haystack/needle obligations as flattened
    token lists. Substitutions are broadcast through `subst_sink_i` so each
    obligation stays synchronized with the current representatives.

    `ncontains_propagation` performs a length gate and a deterministic
    prefix-unrolling search. A determined match is a conflict; a determined
    mismatch can shorten or discharge the obligation; unresolved variable
    alignments stay pending. An empty needle is an immediate conflict.

    `m_ncs` is append-only: removing or replacing an obligation only flips
    `m_active`, and replacements append a shortened obligation to the end.
    `m_qhead` records the first obligation that still needs scanning;
    `apply_subst` rewinds it when a substitution can invalidate an earlier
    "no further progress" verdict.

Author:

    Nikolaj Bjorner (nbjorner) 2026
    Clemens Eisenhofer 2026
    Margus Veanes 2026

--*/
#pragma once

#include "ast/ast.h"
#include "ast/seq_decl_plugin.h"
#include "ast/arith_decl_plugin.h"
#include "ast/seq/seq_eq_facet.h"
#include "util/stx_search_tree.h"
#include "util/trail.h"
#include <algorithm>

namespace seq {

    // One pending negative-containment obligation: `m_needle` does not
    // occur as an infix of `m_haystack`, represented as flattened token
    // lists so substitutions keep it in sync.
    //
    // The representation is append-only. Removing or replacing an
    // obligation just flips `m_active`; replacements append the shortened
    // obligation to the end. Iterators must skip inactive entries.
    struct str_ncontains : public stx::constraint_i {
        expr_ref_vector m_haystack;
        expr_ref_vector m_needle;
        eq_tree::dep_tracker m_dep;
        bool            m_active = true;
        str_ncontains(expr_ref_vector const& h, expr_ref_vector const& n, eq_tree::dep_tracker dep = nullptr) :
            m_haystack(h), m_needle(n), m_dep(dep) {}
        bool active() const { return m_active; }

        // -- stx::constraint_i (unsat-cache identity) --
        // Identity is (haystack, needle) - directional, unlike
        // eq_facet::equation, so no canonical lhs/rhs swap is needed
        // (h not-contains n and n not-contains h are different facts).
        // `clone()` intentionally drops `m_dep`/`m_active` - see
        // stx::constraint_i's class comment.
        uint64_t hash() const override;
        bool equals(stx::constraint_i const& other) const override;
        stx::constraint_i* clone() const override { return alloc(str_ncontains, m_haystack, m_needle); }
        void* dep_handle() const override { return m_dep; }
    };

    /**
     * Facet holding a set of pending negative str.contains obligations.
     * See module comment for the propagation responsibilities.
     */
    class ncontains_facet : public stx::facet_i, public subst_sink_i {
        ast_manager& m;
        seq_util&    u;
        eq_tree::dep_manager_t& m_dm;
        vector<str_ncontains> m_ncs;
        // First obligation not yet known to be at a fixed point for the
        // current node. `ncontains_propagation` scans only
        // `[m_qhead, m_ncs.size())`. `apply_subst` rewinds it to the
        // earliest touched active obligation.
        unsigned m_qhead = 0;

    public:
        ncontains_facet(trail_stack& trail, ast_manager& m, seq_util& u, eq_tree::dep_manager_t& dm) :
            facet_i(trail), m(m), u(u), m_dm(dm) {}

        ast_manager& get_manager() const { return m; }
        seq_util& get_seq_util() const { return u; }

        // Trailed add.
        void add_ncontains(expr_ref_vector const& h, expr_ref_vector const& n, eq_tree::dep_tracker dep = nullptr) {
            m_ncs.push_back(str_ncontains(h, n, dep));
            m_trail.push(push_back_trail<str_ncontains>(m_ncs));
        }
        // Convenience overload: splits haystack/needle into concat units
        // and delegates to the trailed vector form above.
        void add_ncontains(expr* haystack, expr* needle, eq_tree::dep_tracker dep = nullptr) {
            expr_ref_vector hts(m), nts(m);
            u.str.get_concat_units(haystack, hts);
            u.str.get_concat_units(needle, nts);
            add_ncontains(hts, nts, dep);
        }

        vector<str_ncontains> const& ncontains() const { return m_ncs; }
        unsigned qhead() const { return m_qhead; }

        // Advance `m_qhead` forward. Trailed.
        void advance_qhead(unsigned head);

        // Rewind `m_qhead` to `idx` when a substitution touches an
        // already-scanned obligation. Trailed.
        void rewind_qhead(unsigned idx);

        // Drop `idx`'s obligation by flipping `m_active`. Trailed.
        void remove(unsigned idx);

        // Replace `idx` with a fresh obligation over `new_haystack`.
        // Used when deterministic prefix-unrolling strips a leading run.
        void replace_with_tail(unsigned idx, expr_ref_vector const& new_haystack);

        // Broadcast a substitution so haystack and needle stay in sync with
        // the shared variable pool. Joins `subst_dep` into the touched
        // obligation's dependency.
        void apply_subst(expr* var, expr_ref_vector const& repl, eq_tree::dep_tracker subst_dep) override;

        // -- stx::facet_i --
        stx::facet_i* clone(trail_stack& trail) const override;
        bool is_satisfied() const override { return std::all_of(m_ncs.begin(), m_ncs.end(), [](str_ncontains const& nc) { return !nc.active(); }); }
        std::ostream& display(std::ostream& out) const override;

        // -- unsat-cache signature --
        // An active `not contains(h,n)` obligation determines
        // (in)consistency directly (see is_satisfied()), so it always
        // participates.
        bool contributes_to_signature() const override { return true; }
        void append_constraints(vector<stx::constraint_i const*>& out) const override;
    };

    // Length-gate propagation plus deterministic prefix-unrolling. Each
    // step either shortens the haystack, decides the obligation, or leaves
    // it pending until substitutions resolve more token equalities.
    // Incremental via `f.qhead()`: only `[qhead, ncontains().size())` is
    // scanned each call.
    class ncontains_propagation : public eq_tree::propagation_plugin_i {
        ast_manager&  m;
        seq_util&     u;
        arith_util&   a;
        struct stats {
            unsigned m_num_propagate = 0;
            void reset() { *this = stats(); }
        };
        stats m_stats;
    public:
        ncontains_propagation(ast_manager& m, seq_util& u, arith_util& a) :
            m(m), u(u), a(a) {}
        char const* name() const override { return "ncontains-propagate"; }
        stx::simplify_result propagate(eq_tree::node& n) override;
        void collect_statistics(::statistics& st) const override { st.update("seq-ncontains-propagate num calls", m_stats.m_num_propagate); }
        void reset_statistics() override { m_stats.reset(); }
    };

} // namespace seq
