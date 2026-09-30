/*++
Copyright (c) 2026 Microsoft Corporation

Module Name:

    seq_req_facet.h

Abstract:

    Regular-expression equality/disequality facet.

    Regex equalities and disequalities cannot go through `eq_facet` or
    `deq_facet`, because regex terms do not decompose into sequence tokens.

    `req_facet` stores pending `(p, q, is_eq)` obligations. `req_propagation`
    resolves them with `seq::regex_bisim`:
      - `l_true`: the languages are equivalent, so equalities are discharged
        and disequalities conflict;
      - `l_false`: the languages differ, so disequalities are discharged and
        equalities conflict;
      - `l_undef`: the request stays pending.

    `m_qhead` tracks the first request not yet examined by propagation.

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
        // First request not yet examined by `req_propagation`. Trailed like
        // any other facet-owned scalar.
        unsigned m_qhead = 0;

    public:
        req_facet(trail_stack& trail, ast_manager& m, seq_util& u, eq_tree::dep_manager_t& dm) :
            facet_i(trail), m(m), u(u), m_dm(dm) {}

        ast_manager& get_manager() const { return m; }
        seq_util& get_seq_util() const { return u; }

        // Trailed add.
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

    // Run `seq::regex_bisim` on each pending request at index >= qhead().
    // Requests are examined once: this facet never rewrites pending `p/q`,
    // so re-running the same undecided request would not help.
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
            st.update("seq-req-propagate num calls", m_stats.m_num_propagate);
            st.update("seq-req-propagate num resolved", m_stats.m_num_resolved);
        }
        void reset_statistics() override { m_stats.reset(); }
    };

} // namespace seq
