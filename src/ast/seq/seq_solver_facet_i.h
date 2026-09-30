/*++
Copyright (c) 2026 Microsoft Corporation

Module Name:

    seq_solver_facet_i.h

Abstract:

    Abstract interface for the arithmetic (length) facet.

    Facets under `ast/seq` use this header to read and update
    branch-local arithmetic state without depending on the concrete
    `smt::solver_facet` implementation under `src/smt`.

Author:

    Nikolaj Bjorner (nbjorner) 2026
    Clemens Eisenhofer 2026
    Margus Veanes 2026

--*/
#pragma once

#include "ast/ast.h"
#include "ast/arith_decl_plugin.h"
#include "ast/seq/seq_eq_facet.h"
#include "util/stx_search_tree.h"

namespace seq {

    /**
     * Abstract interface for the arithmetic (length) facet.
     */
    class solver_facet_i : public stx::facet_i {
    public:
        explicit solver_facet_i(trail_stack& trail) : facet_i(trail) {}
        ~solver_facet_i() override = default;

        virtual arith_util& get_arith_util() = 0;

        // Record one more length (or other arithmetic) constraint owned
        // by the current branch. `dep` (if non-null) is the dependency
        // justifying `c`. Returns true iff `c` was newly recorded.
        virtual bool add_constraint(expr* c, eq_tree::dep_tracker dep = nullptr) = 0;

        // Generate `len(lhs) = len(rhs)` from an eq_facet equation and
        // record it via add_constraint, tagged with `dep`. Returns true
        // iff at least one new constraint was recorded.
        virtual bool add_length_constraint(expr_ref_vector const& lhs, expr_ref_vector const& rhs, eq_tree::dep_tracker dep = nullptr) = 0;

        virtual bool has_conflict() const = 0;

        // Dependency justifying the current conflict (valid iff
        // has_conflict()); may be nullptr (sound, just less precise).
        virtual eq_tree::dep_tracker conflict_dep() const = 0;

        // Query the shared incremental backend for whether `c` is
        // currently implied by the asserted constraint set, without
        // adding it permanently.
        // On l_true, `*core` (if given) justifies the implication.
        virtual lbool implies(expr* c, eq_tree::dep_tracker* core = nullptr) const = 0;
        // numeral value of `e` in the arithmetic model: the live one, or the one captured at a sat leaf
        virtual bool value(expr* e, rational& v) const = 0;
    };

} // namespace seq
