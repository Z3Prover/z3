/*++
Copyright (c) 2026 Microsoft Corporation

Module Name:

    seq_arith_facet.h

Abstract:

    Arithmetic (length) facet ("Phase 4" of the modular plugin-based search
    tree design, following the `stx::` core in util/stx_search_tree.h and
    the `eq_facet`/`deq_facet` facets in ast/rewriter/seq_eq_facet.h).

    This is the first facet that wraps a genuine incremental SMT backend
    (per z3papers/nseq/facet-arith.md's `sub_solver_i`): rather than
    reasoning about length/arithmetic constraints itself, `arith_facet`
    delegates satisfiability of a set of integer-linear-arithmetic
    constraints (derived from `eq_facet`'s equations via `str.len`) to a
    real `solver` instance (see src/solver/solver.h,
    src/smt/smt_solver.h's `mk_smt_solver`), kept alive for the whole
    search and pushed/popped in lockstep with the search tree's DFS
    backtracking via the new `facet_i::on_enter()`/`on_leave()` hooks
    (see the "Phase 4" note at the top of util/stx_search_tree.h).

    Design simplifications relative to the full facet-arith.md spec (left
    for later, since no `mem_facet` exists yet to feed Parikh-image /
    regex-membership constraints):
      - Only length constraints are generated: for each pending equation
        `L = R` held by `eq_facet`, `arith_facet` asserts
        `len(L) = len(R)` (as a sum of `str.len` over each token: a
        constant token contributes 1, a variable token contributes
        `str.len(v)`), plus `len(v) >= 0` for every variable it has not
        already constrained. This alone is enough to refute equations
        like `a ++ X = X ++ b` with `a != b` (see facet-arith.md section
        3.1's simplest case): any solution has `len(a++X) = len(X++b)`,
        i.e. `1 + len(X) = len(X) + 1`, which is not a contradiction by
        itself for *this* equation alone, but combined with iterating
        Nielsen branches that never terminate, the arithmetic facet's
        real payoff appears once a `mem_facet`/exponent argument is
        layered on. For this phase, `arith_facet` is deliberately kept as
        infrastructure: a real incremental backend, wired to push/pop
        with the tree, generating and checking length constraints - not a
        complete decision procedure for periodicity by itself.
      - No model extraction / no consequence-finding: `arith_facet` only
        asks `check()` for `sat`/`unsat`/`unknown` on the accumulated
        constraint set; `unknown` is folded into the facet reporting
        "unresolved" (never itself conflicting or being satisfied), so it
        can never cause a false verdict, only a possible loss of
        precision (soundness preserved, exactly as `deq_facet`'s
        documented incompleteness in Phase 3).
      - No fresh-constraint deduplication across nodes beyond what
        `eq_facet`'s own equation-set already provides; nodes are
        immutable/persistent so this facet's own vector of constraints is
        always exactly "this node's own new asserts" (see the `on_enter`
        design note below), which is what push/pop needs.

Author:

    Nikolaj Bjorner (nbjorner) 2026

--*/
#pragma once

#include "ast/ast.h"
#include "ast/seq_decl_plugin.h"
#include "ast/arith_decl_plugin.h"
#include "ast/rewriter/seq_eq_facet.h"
#include "util/stx_search_tree.h"
#include "util/params.h"

class solver;

namespace seq {

    /**
     * Thin incremental-arithmetic backend abstraction (per
     * z3papers/nseq/facet-arith.md's `sub_solver_i`), wrapping a single
     * shared `solver` instance for the whole search (see
     * src/solver/solver.h, src/smt/smt_solver.h). One instance is shared
     * by every `arith_facet` clone in the tree (they all describe the
     * same underlying incremental scope stack, kept in sync with DFS
     * backtracking via `facet_i::on_enter`/`on_leave`).
     */
    class arith_sub_solver {
        ast_manager& m;
        solver*      m_solver; // owned

    public:
        arith_sub_solver(ast_manager& m, arith_util& a);
        ~arith_sub_solver();

        void assert_expr(expr* e);
        void push();
        void pop(unsigned n);
        unsigned get_scope_level() const;
        lbool check();
    };

    /**
     * Facet holding this node's own newly-added length constraints (over
     * and above whatever its ancestors already pushed into the shared
     * `arith_sub_solver`). Since nodes in `stx::search_tree` are
     * immutable/persistent (a child is a clone of its parent plus one
     * incremental change), a fresh `arith_facet` clone's own constraint
     * vector naturally holds exactly the constraints *this* node adds -
     * `on_enter()` asserts precisely those and pushes a new backend scope;
     * `on_leave()` pops it. This mirrors facet-arith.md section 2's
     * "push/pop synced to DFS scope" requirement without the generic
     * `stx::` engine needing to know anything about incremental solvers.
     */
    class arith_facet : public stx::facet_i {
        ast_manager&      m;
        arith_util        a;
        seq_util&         u;
        arith_sub_solver& m_solver;
        expr_ref_vector   m_own;       // constraints added at this node only
        bool              m_scope_pushed = false; // true once on_enter() has pushed this node's scope
        bool              m_conflict = false; // true if the shared solver went unsat after the last add_constraint

    public:
        arith_facet(ast_manager& m, seq_util& u, arith_sub_solver& solver) :
            m(m), a(m), u(u), m_solver(solver), m_own(m) {}

        ast_manager& get_manager() const { return m; }
        arith_util& get_arith_util() { return a; }
        seq_util& get_seq_util() const { return u; }

        // Record one more length (or other arithmetic) constraint owned by
        // this node. `on_enter()` has already pushed this node's own
        // backend scope by the time any propagation plugin can run, so
        // the constraint is asserted into the shared backend immediately
        // and satisfiability is rechecked - this keeps the "assert as
        // soon as discovered, pop on backtrack" discipline correct even
        // for constraints discovered *after* on_enter() (e.g. from an
        // equation eq_facet only simplified into existence during this
        // very DFS node's own propagation pass).
        void add_constraint(expr* c);

        // Generate `len(lhs) = len(rhs)` (as an expr over str.len of each
        // token-list side, per the module comment) from an eq_facet
        // equation and record it via add_constraint. Also records
        // `len(v) >= 0` once per fresh variable token seen.
        void add_length_constraint(token_list const& lhs, token_list const& rhs);

        // -- stx::facet_i --
        stx::facet_i* clone() const override;
        unsigned hash() const override;
        bool similar(facet_i const& other) const override;
        // arith_facet never itself declares the search "done": it only
        // ever prunes (conflict) or stays silent, deferring the sat
        // verdict to the other facets (eq_facet/deq_facet's own
        // is_satisfied()).
        bool is_satisfied() const override { return false; }

        void on_enter() override;
        void on_leave() override;

        bool has_conflict() const { return m_conflict; }
    };

    // Deterministic propagation plugin: reads eq_facet's current equation
    // set (facet id `eq_id`) and feeds any not-yet-seen equation's length
    // constraint into arith_facet (facet id `arith_id`), then checks the
    // shared incremental backend. Constraints are generated once (the
    // simplify pass here is not idempotency-guarded beyond `eq_facet`'s
    // own dedup via propagate_to_fixpoint's hashing - see module comment
    // for the "no cross-node dedup beyond eq_facet's own set" caveat).
    class arith_propagation : public eq_tree::propagation_plugin_i {
        stx::facet_id m_arith_id;
        stx::facet_id m_eq_id;
    public:
        arith_propagation(stx::facet_id arith_id, stx::facet_id eq_id) :
            m_arith_id(arith_id), m_eq_id(eq_id) {}
        char const* name() const override { return "arith-propagate"; }
        stx::simplify_result propagate(eq_tree::node& n) override;
    };

} // namespace seq
