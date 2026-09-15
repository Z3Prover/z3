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
#include "ast/seq/seq_ambient_context.h"
#include "util/stx_search_tree.h"
#include "util/trail.h"

namespace seq {

    /**
     * Facet accumulating side assumptions (Boolean literals) picked up
     * during search that the main SMT context must also make hold for
     * any model extracted from a satisfiable node to be valid. Unlike
     * every other facet, `assumption_facet` never itself simplifies,
     * propagates, or splits: it is a pure accumulator, consulted only by
     * `theory_nseq` when a satisfiable node is reported (see
     * theory_nseq.cpp), which must ensure every accumulated assumption
     * is (or becomes) true in the ambient context before the search
     * tree's model can be trusted.
     *
     * A typical source is `word_eq_split`'s "neither equal nor distinct"
     * arm (facet-eq-deq.md, seq_eq_facet.cpp around word_eq_split): two
     * symbolic (non-value) character terms that reduce_eq/word_eq_split
     * cannot statically resolve are forced to coincide via a term
     * substitution, but that substitution is only sound in models where
     * the two characters actually are equal - so the equality is also
     * recorded here (and separately asserted to the arithmetic
     * sub-solver via solver_facet_i::add_constraint) so that
     * `theory_nseq` can, at satisfiability time, either confirm the
     * ambient context already assigns the corresponding literal true or
     * force it so (see module comment on theory_nseq.cpp's satisfiable
     * handling).
     */
    class assumption_facet : public stx::facet_i {
        ast_manager&    m;
        expr_ref_vector m_assumptions;
    public:
        assumption_facet(trail_stack& trail, ast_manager& m) :
            facet_i(trail), m(m), m_assumptions(m) {}

        ast_manager& get_manager() const { return m; }

        // Trailed: all constraint additions are trailed, no exception.
        // Undo just pops the pushed element.
        void add_assumption(expr* a) {
            m_assumptions.push_back(a);
            m_trail.push(push_back_vector(m_assumptions));
        }

        // Records `a` as an assumption (as above, and skipping the
        // re-add if `a` is already present - e.g. because an earlier
        // call, possibly for a different tree edge, already added it)
        // and also registers it as a conditional dependency with the
        // ambient context, so a caller can attach the returned
        // dep_tracker_t to whatever hypothetical constraint (e.g. a
        // view_witness assertion) relies on `a`, instead of calling
        // add_assumption(a) and ac.add_conditional_dep(a) separately. A
        // fresh conditional-dep leaf is always minted and returned, even
        // when `a` was already recorded, since distinct call sites/edges
        // each need their own dep_tracker_t handle.
        template <typename dep_tracker_t>
        dep_tracker_t add_assumption(expr* a, ambient_context_i<dep_tracker_t>& ac) {
            if (!m_assumptions.contains(a))
                add_assumption(a);
            return ac.add_conditional_dep(a);
        }

        expr_ref_vector const& assumptions() const { return m_assumptions; }

        // -- stx::facet_i --
        facet_i* clone(trail_stack& trail) const override {
            assumption_facet* f = alloc(assumption_facet, trail, m);
            f->m_assumptions.append(m_assumptions);
            return f;
        }
        bool is_satisfied() const override { return true; } // never blocks satisfiability on its own
        std::ostream& display(std::ostream& out) const override {
            out << "assumption_facet: " << m_assumptions.size() << " assumption(s)\n";
            for (expr* a : m_assumptions) out << "  " << mk_pp(a, m) << "\n";
            return out;
        }
    };

} // namespace seq
