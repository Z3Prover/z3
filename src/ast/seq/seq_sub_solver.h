/*++
Copyright (c) 2026 Microsoft Corporation

Module Name:

    seq_sub_solver.h

Abstract:

    Abstract incremental-arithmetic backend interface `sub_solver_i`.

    `solver_facet` owns the concrete backend and exposes it through this
    interface. The backend models a branch-local state `S_s = S_m + L_s`,
    where `S_m` is the ambient solver state and `L_s` are branch
    assumptions. Its model should prefer the main solver's current length
    values when available and must respect its known lower and upper
    bounds. If the backend is satisfiable, assumptions from `L_s` must be
    adopted by the main solver unless they are already implied.
   
Author:

    Nikolaj Bjorner (nbjorner) 2026

--*/
#pragma once

#include "ast/ast.h"
#include "util/ref.h"
#include "ast/seq/seq_eq_facet.h"

class model;
typedef ref<model> model_ref;

namespace seq {

    /**
     * Abstract incremental-arithmetic backend interface. `solver_facet`
     * uses this surface without depending on any concrete solver type.
     * One backend instance is shared by all `solver_facet` clones in the
     * tree and kept in sync with DFS backtracking by
     * `facet_i::on_enter`/`on_leave`.
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
        // model of the current constraints, if they are satisfiable
        virtual bool get_model(model_ref& md) { return false; }
    };

} // namespace seq
