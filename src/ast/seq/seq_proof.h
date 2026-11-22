/*++
Copyright (c) 2026 Microsoft Corporation

Module Name:

    seq_proof.h

Abstract:

    Domain proof DAG for sequence search. Refutations are conditional on
    fact-level derivations with scoped branch closure.

--*/
#pragma once

#include "ast/seq/seq_eq_facet.h"
#include <functional>
#include <memory>
#include <vector>

namespace seq {

    class mem_facet;
    struct view;

    class proof_tracker : public eq_tree::proof_tracker_i {
        struct frame {
            expr_ref m_initial;
            proof_ref_vector m_premises;
            expr_ref_vector m_context;
            symbol m_incoming;
            bool m_complete = true;

            frame(ast_manager& m, expr* state, char const* rule) :
                m_initial(state, m), m_premises(m), m_context(m),
                m_incoming(rule ? symbol(rule) : symbol::null) {}
        };

        ast_manager& m;
        seq_util u;
        proof_manager& m_dm;
        proof_ref m_proof;
        expr_ref m_fact;
        expr_ref m_root_state;
        std::function<void(expr_ref_vector&)> m_context_facts;
        expr_ref_vector m_context;
        std::vector<std::unique_ptr<frame>> m_stack;
        proof_ref_vector m_pending;
        proof_ref_vector m_inputs;

        expr_ref snapshot(eq_tree::node const& n);
        expr_ref conditional_state(expr* state, expr_ref_vector const& context);
        void collect_context(eq_tree::node const& n, frame& f);
        static void append_context(expr_ref_vector const& src, expr_ref_vector& dst);
        void collect_proofs(eq_tree::node const& n, proof_ref_vector& proofs);
        void append_facts(stx::facet_i const& f, expr_ref_vector& facts);
        void append_equality(expr_ref_vector const& lhs, expr_ref_vector const& rhs,
                             bool equality, expr_ref_vector& facts);
        sort* side_sort(expr_ref_vector const& lhs, expr_ref_vector const& rhs);

    public:
        proof_tracker(ast_manager& m, proof_manager& dm);
        // Called at each begin(), after each reported propagation, and at
        // each end(), with a fresh empty output vector. May return a delta
        // or cumulative facts: AST-identical facts are deduplicated. Output
        // must include the external premises needed by the preceding step,
        // including newly discovered ambient dependencies. Each fact must
        // be eligible as an enclosing-context theorem premise, NOT a
        // branch-only guard, fresh branch definition, or backend assumption
        // literal. The caller must discharge the final get_fact(), including
        // these external premises. Branch guards/definitions stay in facets
        // and are discharged only by named split closures.
        // An ambient context requires an explicit callback; an empty output
        // is valid if the step needs no additional external premises.
        // Configure outside an active search. reset() retains the callback
        // but clears all captured facts, proofs, and frames.
        void set_context_facts(std::function<void(expr_ref_vector&)> callback) {
            m_context_facts = std::move(callback);
        }
        void reset() override;
        void begin(eq_tree::node const& n, char const* rule) override;
        void start_step(eq_tree::node const& n, char const* rule, bool branch) override;
        void finish_step(eq_tree::node const& n, char const* rule, bool committed) override;
        void propagate(eq_tree::node const& n, char const* rule) override;
        void end(eq_tree::node const& n, stx::search_result result) override;

        // Borrowed pointers. The proof survives until reset()/root begin();
        // the fact can change at the next callback, so retain an expr_ref
        // when keeping an earlier version across callbacks.
        // get_fact() is root facet state AND the union of external premises
        // observed so far; it can grow at each callback. For unsat, get_proof()
        // concludes get_fact() => false. No proof is published for sat,
        // unknown, or depth cutoff; their captured facts last until reset().
        proof* get_proof() const { return m_proof.get(); }
        expr* get_fact() const { return m_fact.get(); }
        void append_input_proofs(proof_ref_vector& proofs) const;
    };

}
