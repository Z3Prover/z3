/*++
Copyright (c) 2026 Microsoft Corporation

Module Name:

    seq_assumption_facet.h

Abstract:

    Facet accumulating side assumptions (Boolean literals) picked up
    during search that the main SMT context must also make hold for
    any model extracted from a satisfiable node to be valid.

Author:

    Nikolaj Bjorner (nbjorner) 2026

--*/
#pragma once

#include "ast/ast.h"
#include "ast/ast_pp.h"
#include "ast/seq/seq_proof_manager.h"
#include "ast/seq/seq_ambient_context.h"
#include "util/stx_search_tree.h"
#include "util/trail.h"
#include <utility>

namespace seq {

    /**
     * Pure accumulator of branch-local Boolean assumptions that must
     * also hold in the ambient SMT context for a satisfiable node's
     * model to be valid.
     *
     * A typical source is a search step that substitutes one symbolic
     * character term for another under an equality that is not yet
     * known globally. The equality is recorded here, and also fed to
     * the arithmetic facet, so it can be checked or enforced before the
     * node is reported satisfiable.
     */
    class assumption_facet : public stx::facet_i {
        using dep_tracker_t = stx::search_tree<unsigned>::dep_tracker;

        ast_manager& m;
        struct assumption {
            expr_ref first;
            dep_tracker_t second;
            proof_ref m_proof;
            assumption(ast_manager& m, expr* fact, dep_tracker_t dep, proof* pr) :
                first(fact, m), second(dep), m_proof(pr, m) {}
        };
        vector<assumption> m_assumptions;
        proof_manager* m_dm;
        bool m_model_completion_blocked = false;

        void cache_assumption(expr* a, dep_tracker_t dep, proof* premise, symbol const& rule) {
            proof_ref pr(m);
            if (m.proofs_enabled())
                pr = m_dm ? (premise ? m_dm->mk_proof(rule, a, {premise}) : m_dm->mk_proof(rule, a)) : m.mk_hypothesis(a);
            m_assumptions.push_back(assumption(m, a, dep, pr));
            m_trail.push(push_back_vector(m_assumptions));
        }

    public:
        assumption_facet(trail_stack& trail, ast_manager& m, proof_manager* dm = nullptr) :
            facet_i(trail), m(m), m_dm(dm) { if (dm) dm->set_manager(m); }

        ast_manager& get_manager() const { return m; }

        // Return the cached dependency for `a`, or register and cache one.
        dep_tracker_t add_assumption(expr* a, ambient_context_i<dep_tracker_t>& ac, proof* premise = nullptr,
                                     symbol const& rule = symbol("seq-assume")) {
            for (auto const& entry : m_assumptions)
                if (entry.first == a)
                    return entry.second;
            dep_tracker_t dep = ac.add_conditional_dep(a);
            cache_assumption(a, dep, premise, rule);
            return dep;
        }

        vector<assumption> const& assumptions() const { return m_assumptions; }
        bool model_completion_blocked() const { return m_model_completion_blocked; }
        void block_model_completion() {
            if (m_model_completion_blocked)
                return;
            m_trail.push(value_trail<bool>(m_model_completion_blocked));
            m_model_completion_blocked = true;
        }

        // -- stx::facet_i --
        facet_i* clone(trail_stack& trail) const override {
            assumption_facet* f = alloc(assumption_facet, trail, m, m_dm);
            f->m_assumptions.append(m_assumptions);
            f->m_model_completion_blocked = m_model_completion_blocked;
            return f;
        }
        bool is_satisfied() const override { return true; } // never blocks satisfiability on its own
        std::ostream& display(std::ostream& out) const override {
            out << "assumption_facet: " << m_assumptions.size() << " assumption(s)\n";
            for (auto const& assumption : m_assumptions)
                out << "  " << mk_pp(assumption.first, m) << "\n";
            return out;
        }
    };

} // namespace seq
