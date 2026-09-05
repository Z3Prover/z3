/*++
Copyright (c) 2026 Microsoft Corporation

Module Name:

    seq_sub_solver.h

Abstract:

    Abstract incremental-arithmetic backend interface (`sub_solver_i`,
    per z3papers/nseq/facet-arith.md), factored out of
    smt/seq_solver_facet.h so that facets living in ast/seq (which must
    not depend on anything under src/smt) can reference the interface
    without pulling in the concrete `smt::seq_solver_facet.h`/`arith_facet`
    module (which does depend on src/solver and is compiled as part of
    the `smt` component, itself a consumer of `ast_seq` - the reverse
    dependency direction would create a cycle).

    `arith_facet` (smt/seq_solver_facet.h) is the only concrete consumer
    that owns/constructs a `sub_solver_i` instance (via `sub_solver`);
    ast/seq facets such as `ncontains_facet`/`power_facet` only ever see
    `arith_facet` referenced by id through `stx::node::facet_as<>`, so
    they do not even need this header directly for that - but they do
    reference `arith_facet` by name in the propagation plugins that
    consult it, which is why this split keeps the interface (not the
    concrete backend) as the shared, dependency-direction-safe piece.

    This mirrors the c3 branch's `seq::sub_solver_i`
    (src/smt/seq/seq_nielsen.h): `assert_expr` takes an optional
    `dep_tracker` justification (built via the caller's own
    `eq_tree::dep_manager_t`, e.g. `eq_facet::dm()`/`arith_facet`'s
    caller); a `nullptr` dep means "unconditional fact" (asserted
    directly, never retracted from an unsat core), while a non-null dep
    ties the assertion to a fresh internal assumption literal so that,
    should `check()` return `l_false`, `unsat_core()` can return the
    join of exactly the deps of the assertions that contributed to that
    particular UNSAT result - the same "dependency-tracked constraint"
    discipline `arith_propagation`/`power_propagation`/`power_split` use
    when asserting length axioms derived from a specific equation/
    obligation (whose own justification must be threaded through so a
    resulting conflict's dependency is precise, not `nullptr`).

Author:

    Nikolaj Bjorner (nbjorner) 2026

--*/
#pragma once

#include "ast/ast.h"
#include "ast/seq/seq_eq_facet.h"

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

        // Assert `e`. If `dep` is null, `e` is an unconditional fact of
        // the backend's state (asserted directly, e.g. `len(v) >= 0`);
        // otherwise `e` is tied to `dep` so that, should a later check()
        // report `l_false`, `unsat_core()` can report whether this
        // particular assertion contributed to the conflict.
        virtual void assert_expr(expr* e, eq_tree::dep_tracker dep = nullptr) = 0;
        virtual void push() = 0;
        virtual void pop(unsigned n) = 0;
        virtual unsigned get_scope_level() const = 0;
        virtual lbool check() = 0;

        // Valid only immediately after a check() that returned `l_false`:
        // the join of the deps of every dependency-tracked assertion
        // (per the `assert_expr` contract above) that appears in the
        // backend's own UNSAT core. Returns `nullptr` if no
        // dependency-tracked assertion contributed (e.g. the conflict is
        // purely among unconditional facts) - never a false "no
        // dependency" claim about a real contributing dep, so it is
        // always sound to use as a conflict's justification.
        virtual eq_tree::dep_tracker unsat_core() const { return nullptr; }
    };

} // namespace seq
