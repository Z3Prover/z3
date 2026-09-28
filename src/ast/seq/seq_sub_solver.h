/*++
Copyright (c) 2026 Microsoft Corporation

Module Name:

    seq_sub_solver.h

Abstract:

    Abstract incremental-arithmetic backend interface `sub_solver_i`.

    `solver_facet` (smt/seq_solver_facet.h) is the only concrete consumer
    that owns/constructs a `sub_solver_i` instance (via `sub_solver`).

    Interface requirements:

    S_m - the main solver state based on asserted literals 
    M_m - model of the main solver state (for arithmetic variables)
    S_s - the sub-solver state during search
    M_s - model of the sub-solver state
    L_s - assumption literals asserted on the sub-solver state

    We will assume a relation between S_m and S_s by 
    
             S_s = S_m + L_s

   M_m(|x|) in N_\bot - current assignment to length |x| term in main solver. \bot if there are no assignments
   S_m(|x|_lo) in N_\bot - forced lower bound in main solver
   S_m(|x|_hi) in N_\bot - forced upper bound in main solver

   Assumption on model construction by search tree:
   
      Preferred: |M_s(|x|)| = M_m(|x|) if M_m(|x|) \neq \bot 
      Required: S_m(|x|_lo) <= |M_s(|x|)| <= S_m(|x|_hi)

   In other words, the string x is preferrably to be assigned values that are consistent with the current model.

   If the subsolver ends in a satisfiable state, then literals in L_s are assumed if they are not already true in M_m / S_m.
   
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
     * Abstract incremental-arithmetic backend interface (per
     * z3papers/nseq/facet-arith.md's `sub_solver_i`). `solver_facet` is
     * built entirely against this interface - it has no dependency on
     * `src/solver/solver.h` or any concrete solver implementation. One
     * instance is shared by every `solver_facet` clone in the tree (they
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
        // model of the current constraints, if they are satisfiable
        virtual bool get_model(model_ref& md) { return false; }
    };

} // namespace seq
