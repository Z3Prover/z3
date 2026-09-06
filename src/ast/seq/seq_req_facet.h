/*++
Copyright (c) 2026 Microsoft Corporation

Module Name:

    seq_req_facet.h

Abstract:

    Regular-expression equality/disequality facet.

    `new_eq_eh`/`new_diseq_eh` (smt/theory_nseq.cpp) can be handed a pair of
    regex-sorted (`RE_SORT`) enodes, not just sequence-sorted ones - e.g.
    `(= (str.to_re "a") (re.union (str.to_re "a") (str.to_re "a")))` becomes
    an ordinary congruence equality/disequality between two `RE_SORT`
    terms once both are internalized. Regex terms carry no useful
    "flatten into tokens" decomposition the way sequence terms do
    (`get_concat_units`), so they cannot be handed to `eq_facet`/
    `deq_facet` at all; they need their own facet.

    Deciding regex equality/disequality is exactly what
    `seq::regex_bisim` (ast/rewriter/seq_regex_bisim.h) already does for
    ground regexes, via a union-find bisimulation search on the symbolic
    derivative of the XOR (symmetric difference) of the two regexes (see
    `smt/seq_regex.cpp`'s `propagate_eq`/`propagate_ne`, which call it the
    same way for `str.in_re` derivative-closure regex terms). This facet
    reuses that same decision procedure for standalone `RE_SORT`
    equalities/disequalities asserted directly at the SMT-core level.

    `req_facet` just accumulates pending obligations (`str_req`, one
    `(p, q, is_eq)` request per asserted (dis)equality); `req_propagation`
    (a `propagation_plugin_i`) drains them by running `regex_bisim` on
    each still-`l_undef` entry:
      - `l_true` (p, q are language-equivalent): if `is_eq`, the request
        is confirmed (discharge it); if `!is_eq` (a disequality
        obligation, i.e. "p != q" was asserted), this contradicts the
        obligation - conflict.
      - `l_false` (p, q are language-distinct): the mirror image of the
        above - confirms a disequality obligation, contradicts an
        equality obligation.
      - `l_undef` (bisimulation could not decide within its step bound,
        or hit a non-ground/unsupported regex): the entry is left
        pending (marked `l_undef`, i.e. simply not yet resolved) for a
        future propagation round - e.g. after further rewriting/
        internalization has made one side ground, or simply retried
        (regex_bisim is deterministic on the same input, so a retry only
        helps if the input expressions themselves changed, which nothing
        in this facet currently does - there is no substitution/rewrite
        applied to a pending request; this mirrors ncontains_facet's own
        "leave undecided obligations pending" incompleteness).

    `m_qhead` tracks which of `m_reqs` have already been resolved
    (discharged or confirmed-pending as still-undef so far), so a
    propagation round only re-examines genuinely new requests plus any
    prior `l_undef` entries - mirroring `theory_nseq`'s own axiom-queue
    `m_axioms_head` convention (smt/theory_nseq.h/.cpp).

Author:

    Nikolaj Bjorner (nbjorner) 2026
    Clemens Eisenhofer 2026
    Margus Veanes 2026

--*/
#pragma once

#include "ast/ast.h"
#include "ast/seq_decl_plugin.h"
#include "ast/seq/seq_eq_facet.h"
#include "ast/rewriter/seq_rewriter.h"
#include "util/stx_search_tree.h"
#include "util/trail.h"
#include "util/lbool.h"

namespace seq {

    // One pending regex (dis)equality request: `is_eq` records whether
    // `p = q` (true) or `p != q` (false) was asserted; `m_status` is the
    // bisimulation verdict reached so far for the underlying language
    // question "are p and q language-equivalent?" - `l_undef` until
    // `req_propagation` has resolved it (definitively `l_true`/`l_false`)
    // or given up for now (still `l_undef`, left pending).
    struct str_req {
        expr_ref             m_p;
        expr_ref             m_q;
        bool                 m_is_eq;
        eq_tree::dep_tracker m_dep;
        lbool                m_status = l_undef;
        str_req(ast_manager& m, expr* p, expr* q, bool is_eq, eq_tree::dep_tracker dep = nullptr) :
            m_p(p, m), m_q(q, m), m_is_eq(is_eq), m_dep(dep) {}
        bool operator<(str_req const& other) const;
        bool operator==(str_req const& other) const;
    };

    /**
     * Facet holding a set of pending regex (dis)equality requests. See
     * module comment for the propagation responsibilities.
     */
    class req_facet : public stx::facet_i {
        ast_manager& m;
        seq_util&    u;
        eq_tree::dep_manager_t& m_dm;
        vector<str_req> m_reqs;
        // Index of the first request in m_reqs not yet examined by
        // req_propagation (mirrors theory_nseq::m_axioms_head). Trailed
        // like any other facet-owned scalar (see mark_resolved()).
        unsigned m_qhead = 0;

    public:
        req_facet(trail_stack& trail, ast_manager& m, seq_util& u, eq_tree::dep_manager_t& dm) :
            facet_i(trail), m(m), u(u), m_dm(dm) {}

        ast_manager& get_manager() const { return m; }
        seq_util& get_seq_util() const { return u; }

        // Trailed: for adding a regex (dis)equality request (root
        // construction or mid-search alike - all constraint additions
        // are trailed, no exception).
        void add_req(expr* p, expr* q, bool is_eq, eq_tree::dep_tracker dep = nullptr) {
            m_reqs.push_back(str_req(m, p, q, is_eq, dep));
            m_trail.push(push_back_trail<str_req>(m_reqs));
        }

        vector<str_req> const& reqs() const { return m_reqs; }
        unsigned qhead() const { return m_qhead; }

        // Mark request `idx`'s bisimulation verdict as `status` (l_true/
        // l_false: resolved; l_undef: still pending). Trailed.
        void set_status(unsigned idx, lbool status);

        // Advance m_qhead to `head` (only ever forward). Trailed.
        void advance_qhead(unsigned head);

        // Drop request `idx` entirely (discharged/proved, or refuted -
        // in the refuted case the caller has already registered the
        // conflict before calling this). Trailed.
        void remove(unsigned idx);

        // -- stx::facet_i --
        stx::facet_i* clone(trail_stack& trail) const override;
        bool is_satisfied() const override { return m_reqs.empty(); }
        std::ostream& display(std::ostream& out) const override;
    };

    // Drains req_facet's pending requests by running seq::regex_bisim on
    // each one still at index >= qhead() whose status is l_undef,
    // exactly once per round (regex_bisim is deterministic and nothing
    // here ever rewrites a pending request's p/q, so re-running it on an
    // already-l_undef entry in a *later* round - after qhead has
    // advanced past it - cannot yield a different answer; entries are
    // therefore examined only once each, via m_qhead, not repeatedly
    // polled to a fixpoint the way eq_facet's substitution-driven
    // simplification is).
    class req_propagation : public eq_tree::propagation_plugin_i {
        ast_manager&  m;
        seq_util&     u;
        seq_rewriter& m_rw;
        struct stats {
            unsigned m_num_propagate = 0;
            unsigned m_num_resolved = 0;
            void reset() { *this = stats(); }
        };
        stats m_stats;
    public:
        req_propagation(ast_manager& m, seq_util& u, seq_rewriter& rw) : m(m), u(u), m_rw(rw) {}
        char const* name() const override { return "req-propagate"; }
        stx::simplify_result propagate(eq_tree::node& n) override;
        void collect_statistics(::statistics& st) const override {
            st.update("req-propagate num calls", m_stats.m_num_propagate);
            st.update("req-propagate num resolved", m_stats.m_num_resolved);
        }
        void reset_statistics() override { m_stats.reset(); }
    };

} // namespace seq
