/*++
Copyright (c) 2026 Microsoft Corporation

Module Name:

    seq_stoi_facet.h

Abstract:

    Facet tracking every `str.to_int` (stoi) term seen so far, together
    with the greatest string length `k` for which the inductive
    positional-unfolding axiom (`seq::axioms::stoi_axiom(e, k)`, see
    smt/seq_axioms.h) has already been instantiated for it.

    Unlike a purely passive accumulator (e.g. `assumption_facet`), this
    facet also owns the actual coherence-checking control logic
    (`check_stoi_coherence`, below - ported from the c3 branch's
    `theory_nseq::check_stoi_coherence` of the same name), consulted once
    per final check and before `m_tree.solve()`. It never itself
    simplifies, propagates, or splits the search tree though
    (`is_satisfied()` is always true) - any actual axiom injection back
    into the live SMT context happens only inside the two callbacks
    below, supplied by `theory_nseq` at construction time, keeping this
    (ast/seq-layer) facet itself free of any `smt_context` dependency:
      - `m_instantiate`: instantiates the inductive positional-unfolding
        axiom for a given (term, depth) pair - i.e.
        `seq_axioms_util::add_stoi_axiom(e, k)`.
      - the ambient context's own `add_axiom` (see
        ast/seq/seq_ambient_context.h's `ambient_context_i::add_axiom`,
        the same "mk_axiom" mechanism `seq::axioms`/`smt::seq_axioms`
        already use internally) - used for the explicit upper bound
        clause `check_stoi_coherence` also asserts.

Author:

    Nikolaj Bjorner (nbjorner) 2026

--*/
#pragma once

#include "ast/ast.h"
#include "ast/ast_pp.h"
#include "ast/seq_decl_plugin.h"
#include "ast/arith_decl_plugin.h"
#include "ast/seq/seq_ambient_context.h"
#include "util/stx_search_tree.h"
#include "util/trail.h"
#include <functional>

namespace seq {

    class stoi_facet : public stx::facet_i {
        ast_manager& m;
        seq_util&    u;
        arith_util&  a;
        // (stoi(s) term, max k for which stoi_axiom(term, k) was
        // instantiated). Append-only: a term is only ever added once
        // (dequeue_axiom's own m_axiom_set already dedups), and its
        // depth only ever grows (see set_depth).
        vector<std::pair<expr*, unsigned>> m_terms;

        // Instantiates the inductive positional-unfolding axiom for
        // (term, depth) - set by theory_nseq to
        // `m_ax.add_stoi_axiom(e, k)`.
        std::function<void(expr*, unsigned)> m_instantiate;

    public:
        stoi_facet(trail_stack& trail, ast_manager& m, seq_util& u, arith_util& a) : facet_i(trail), m(m), u(u), a(a) {}

        ast_manager& get_manager() const { return m; }

        // Supplies the (term, depth) -> positional-unfolding-axiom
        // callback; must be set before `check_stoi_coherence` is called.
        void set_instantiate(std::function<void(expr*, unsigned)> f) { m_instantiate = f; }

        // Register `e` (a `str.to_int` application) for coherence
        // tracking, at depth 0. Trailed: on backtrack past the scope
        // where `e` was first seen, it drops back out of tracking.
        void add_term(expr* e) {
            m_terms.push_back({e, 0u});
            m_trail.push(push_back_vector(m_terms));
        }

        vector<std::pair<expr*, unsigned>> const& terms() const { return m_terms; }

        // Record that `stoi_axiom(term, k)` has now been instantiated
        // for `m_terms[idx]`. Trailed via vector_value_trail.
        void set_depth(unsigned idx, unsigned k) {
            m_trail.push(vector_value_trail<std::pair<expr*, unsigned>>(m_terms, idx));
            m_terms[idx].second = k;
        }

        // Ported from the c3 branch's `theory_nseq::check_stoi_coherence`:
        // for every tracked `str.to_int` term, instantiates the inductive
        // positional-unfolding axiom (via `m_instantiate`) once the
        // arithmetic sub-solver (queried through `ac.current_value`) has
        // committed to a concrete length `k` for its argument that is
        // deeper than any previously instantiated for it - together with
        // an explicit upper bound `len(s)=k && stoi(s)>=0 =>
        // stoi(s)<=10^k-1` (asserted via `ac.add_axiom`) that the
        // positional unfolding alone does not provide (digit2int has no
        // arithmetic bounds for symbolic characters). Returns true if no
        // new axioms were needed (the tree's answer, if any, can stand),
        // false if at least one axiom was freshly instantiated (the
        // caller should not commit to whatever `m_tree.solve()` would
        // otherwise report/give up on, since new information is now
        // available).
        template <typename dep_tracker_t>
        bool check_stoi_coherence(ambient_context_i<dep_tracker_t>& ac) {
            if (m_terms.empty())
                return true;

            bool progress = false;

            for (unsigned idx = 0; idx < m_terms.size(); ++idx) {
                auto const& [stoi_e, prev_k] = m_terms[idx];
                expr* s = nullptr;
                VERIFY(u.str.is_stoi(stoi_e, s));

                expr_ref len_expr(u.str.mk_length(s), m);
                rational val;
                if (!ac.current_value(len_expr, val) || !val.is_unsigned())
                    continue;

                unsigned k = val.get_unsigned();
                if (k == 0)
                    continue;  // empty string: handled by the basic stoi_axiom_re axiom

                if (prev_k >= k)
                    continue;  // already instantiated at least this deep

                TRACE(seq, tout << "nseq stoi coherence: instantiating depth " << k
                                << " for " << mk_pp(stoi_e, m) << "\n");

                // Positional unfolding: stoi(s, i) = 10*stoi(s, i-1) + digit(s[i])
                m_instantiate(stoi_e, k);

                // Explicit upper bound: len(s)=k && stoi(s) >= 0 => stoi(s) <= 10^k-1
                // (digit2int for symbolic characters has no arith bounds, so the
                //  positional unfolding alone does not constrain stoi(s) sufficiently)
                {
                    rational max_val(1);
                    for (unsigned i = 0; i < k; ++i)
                        max_val *= 10;
                    --max_val;  // 10^k - 1
                    expr_ref le_max(a.mk_le(stoi_e, a.mk_int(max_val)), m);
                    expr_ref ge0(a.mk_ge(stoi_e, a.mk_int(0)), m);
                    expr_ref len_eq_k(m.mk_eq(len_expr, a.mk_int(k)), m);

                    expr_ref_vector clause(m);
                    clause.push_back(m.mk_not(len_eq_k));
                    clause.push_back(m.mk_not(ge0));
                    clause.push_back(le_max);
                    ac.add_axiom(clause);
                }

                set_depth(idx, k);
                progress = true;
            }
            return !progress;
        }

        // -- stx::facet_i --
        facet_i* clone(trail_stack& trail) const override {
            stoi_facet* f = alloc(stoi_facet, trail, m, u, a);
            f->m_terms = m_terms;
            f->m_instantiate = m_instantiate;
            return f;
        }
        bool is_satisfied() const override { return true; } // never blocks satisfiability on its own
        std::ostream& display(std::ostream& out) const override {
            out << "stoi_facet: " << m_terms.size() << " term(s)\n";
            for (auto const& [e, k] : m_terms)
                out << "  " << mk_pp(e, m) << " (depth " << k << ")\n";
            return out;
        }
    };

} // namespace seq
