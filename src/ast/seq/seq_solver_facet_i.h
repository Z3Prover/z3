/*++
Copyright (c) 2026 Microsoft Corporation

Module Name:

    seq_solver_facet_i.h

Abstract:

    Abstract base class for the arithmetic (length) facet, factored out
    of smt/seq_solver_facet.h so that facets living in ast/seq (which must
    not depend on anything under src/smt - see seq_sub_solver.h's module
    comment for the same dependency-direction argument applied to
    `sub_solver_i`) can reference the facet's public surface without
    pulling in the concrete `smt::solver_facet` (which owns a real
    `solver` instance and is compiled as part of the `smt` component,
    itself a consumer of `ast_seq` - the reverse dependency direction
    would create a cycle).

    `solver_facet` (smt/seq_solver_facet.h) is the sole concrete
    implementation; every ast/seq plugin that needs to read/mutate the
    arithmetic facet (eq_split, power_propagation, power_split,
    power_fine_wilf, ncontains_facet's length-gate propagation, ...)
    looks it up via `node.facet_as<solver_facet_i>(arith_id)`, exactly as
    they already look up `eq_facet`/`power_facet` by id - only the
    concrete type differs, from a src/smt dependency to an
    src/ast/seq-only one.

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
     * Abstract interface for the arithmetic (length) facet - see
     * smt/seq_solver_facet.h's module comment for the full design
     * rationale and `solver_facet`'s concrete implementation.
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
        virtual lbool implies(expr* c) const = 0;
    };

} // namespace seq
