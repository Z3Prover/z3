/*++
Copyright (c) 2026 Microsoft Corporation

Module Name:

    seq_sub_solver.h

Abstract:

    Abstract incremental-arithmetic backend interface (`sub_solver_i`,
    per z3papers/nseq/facet-arith.md), factored out of
    smt/seq_arith_facet.h so that facets living in ast/seq (which must
    not depend on anything under src/smt) can reference the interface
    without pulling in the concrete `smt::seq_arith_facet.h`/`arith_facet`
    module (which does depend on src/solver and is compiled as part of
    the `smt` component, itself a consumer of `ast_seq` - the reverse
    dependency direction would create a cycle).

    `arith_facet` (smt/seq_arith_facet.h) is the only concrete consumer
    that owns/constructs a `sub_solver_i` instance (via `arith_sub_solver`);
    ast/seq facets such as `ncontains_facet`/`power_facet` only ever see
    `arith_facet` referenced by id through `stx::node::facet_as<>`, so
    they do not even need this header directly for that - but they do
    reference `arith_facet` by name in the propagation plugins that
    consult it, which is why this split keeps the interface (not the
    concrete backend) as the shared, dependency-direction-safe piece.

Author:

    Nikolaj Bjorner (nbjorner) 2026

--*/
#pragma once

#include "ast/ast.h"

namespace seq {

    /**
     * Abstract incremental-arithmetic backend interface (per
     * z3papers/nseq/facet-arith.md's `sub_solver_i`). `arith_facet` is
     * built entirely against this interface - it has no dependency on
     * `src/solver/solver.h` or any concrete solver implementation. One
     * instance is shared by every `arith_facet` clone in the tree (they
     * all describe the same underlying incremental scope stack, kept in
     * sync with DFS backtracking via `facet_i::on_enter`/`on_leave`).
     */
    class sub_solver_i {
    public:
        virtual ~sub_solver_i() = default;
        virtual void assert_expr(expr* e) = 0;
        virtual void push() = 0;
        virtual void pop(unsigned n) = 0;
        virtual unsigned get_scope_level() const = 0;
        virtual lbool check() = 0;
    };

} // namespace seq
