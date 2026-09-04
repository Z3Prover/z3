/*++
Copyright (c) 2026 Microsoft Corporation

Module Name:

    seq_ambient_context.h

Abstract:

    Abstracted bridge into the ambient SMT context (per
    z3papers/nseq/facet-arith.md's `context_solver_i`), factored out so
    that every facet/plugin living under `ast/seq` (which must not depend
    on anything under `src/smt`, see seq_sub_solver.h's module comment)
    can query bounds/values/variable-hood of the surrounding solver
    without any of them depending on a concrete `smt::context`.

    This differs from `facet-arith.md`'s original `context_solver_i` in
    two ways:
      - Every query that used to return raw `literal_vector`/
        `enode_pair_vector`/`literal` justifications now returns (or
        takes an out-param of) a single `eq_tree::dep_tracker` - the same
        opaque provenance handle every facet already threads through
        `apply_subst`/`add_equation`/`set_conflict` etc. The concrete
        implementation (living under `src/smt`, wrapping
        `theory_seq`/`arith_value`) is responsible for converting
        whatever literals/equalities it consulted into one
        `dep_tracker` (via its own `dep_manager_t`), exactly as
        `arith_sub_solver` already converts assumption literals into
        dependencies today (`seq_arith_facet.cpp`).
      - It adds `is_var(expr*)`, replacing the c3 branch's
        `euf::snode::is_var()` (a node in the old `sgraph`/Nielsen-graph
        representation, not applicable here since this design has no
        `snode` at all - see seq_eq_facet.h's module comment). Per the
        token model in z3papers/nseq's README.md section 5.1.1, a token
        is exactly one of unit/power/variable; `is_var` is implemented
        directly on the base class (non-virtual, `!is_power(x) &&
        !is_unit(x) && !m.is_ite(x)`) using the `ast_manager&`/`seq_util&`
        every concrete `ambient_context_i` is now constructed with, so
        every implementation (including `null_ambient_context`, e.g. in
        unit tests with no live `theory_seq` wired up) shares exactly the
        same notion of "variable" and none can silently diverge.

    `ambient_context_i` is intentionally domain-generic over the
    `dep_tracker` type of whichever `eq_tree` instantiation the caller
    is using (see seq_eq_facet.h's `eq_tree` alias) - it is a template on
    `dep_tracker_t` for that reason, not hardcoded to `seq::eq_tree`.

Author:

    Nikolaj Bjorner (nbjorner) 2026

--*/
#pragma once

#include "ast/ast.h"
#include "ast/arith_decl_plugin.h"
#include "ast/seq_decl_plugin.h"
#include "util/stx_search_tree.h"

namespace seq {

    /**
     * Abstracted, dependency-tracked bridge into the ambient SMT context.
     * Concrete implementations (e.g. under src/smt, wrapping
     * `theory_seq`'s `arith_value`/enode machinery) own translating
     * whatever literals/equalities they actually consulted into a single
     * `dep_tracker_t` value via their own dependency manager.
     *
     * `dep_tracker_t` is a template parameter (rather than hardcoding
     * `seq::eq_tree::dep_tracker`) purely so this header has no
     * dependency on any one `stx::search_tree<...>` instantiation; in
     * practice every current user instantiates it with
     * `seq::eq_tree::dep_tracker` (see seq_eq_facet.h).
     *
     * Derives from `stx::ambient_context_base` (util/stx_search_tree.h) -
     * the domain-opaque, method-free marker class that a
     * `stx::search_tree::node` actually stores (`node::ambient()`/
     * `search_tree::set_ambient_context()`), so that an instance
     * constructed here can be handed straight to
     * `search_tree::set_ambient_context()` and later recovered from any
     * facet via `static_cast` (see e.g. `eq_facet::ambient()` below).
     */
    template <typename dep_tracker_t>
    class ambient_context_i : public stx::ambient_context_base {
    protected:
        ast_manager& m;
        seq_util&    u;
    public:
        ambient_context_i(ast_manager& m, seq_util& u) : m(m), u(u) {}
        ~ambient_context_i() override = default;

        // Is `e` a token this facet layer's Nielsen-style split rules may
        // treat as a freely-substitutable "variable" - i.e. neither a
        // power token (`seq.power`, owned exclusively by power_facet's
        // own dedicated rule family: power_propagation/power_split/
        // power_fine_wilf/power_num_cmp/power_split_elim) nor a unit
        // token (`seq.unit`, a single concrete character/element, never
        // itself substitutable) nor an `ite` term (left alone, matching
        // `is_solvable_var`/`eq_solver::is_var`'s treatment). Per the
        // token model in z3papers/nseq's README.md section 5.1.1, a token
        // is exactly one of unit/power/variable, so this predicate - not
        // `is_solvable_var`/`theory_seq::is_var` - is the one every
        // strict three-way token classification (word_eq_split::split,
        // etc.) should consult; it is implemented once here (non-virtual)
        // so every concrete `ambient_context_i` shares exactly the same
        // notion of "variable" and none can silently diverge.
        bool is_var(expr* e) const { return !u.str.is_power(e) && !u.str.is_unit(e) && !m.is_ite(e); }

        // Best current lower/upper bound on the (integer/arithmetic)
        // value of `e` known to the ambient context (e.g. `str.len` of a
        // sequence term), together with the dependency justifying that
        // bound. Returns false if no bound is currently known.
        virtual bool lower_bound(expr* e, rational& lo, dep_tracker_t& dep) = 0;
        virtual bool upper_bound(expr* e, rational& hi, dep_tracker_t& dep) = 0;

        // The ambient context's current concrete value for `e`, if fully
        // determined (e.g. a model value during a final check). Returns
        // false if `e`'s value is not currently pinned down.
        virtual bool current_value(expr* e, rational& v) = 0;

        // If `e` (a Boolean-sorted term) is already asserted false in the
        // ambient context, return a `dep_tracker_t` justifying that;
        // otherwise return `nullptr` (unknown / not yet decided).
        virtual dep_tracker_t literal_if_false(expr* e) = 0;

        // Ask the ambient context to add a standing disequality axiom
        // between `e1` and `e2` (e.g. to seed further theory
        // propagation) - a one-directional export back into the ambient
        // solver, mirroring `context_solver_i::add_diseq_axiom`; it has
        // no return value/dependency since it does not itself resolve
        // anything within the search tree.
        virtual void add_diseq_axiom(expr* e1, expr* e2) = 0;
    };

    // Trivial, always-"unknown" implementation: usable by unit tests (or
    // any facet standing alone with no live ambient SMT context) that
    // only need `is_var` (inherited, non-virtual, from `ambient_context_i`)
    // and can safely treat every bound/value query as "not currently
    // known" - never reports a false bound, only ever a possible loss of
    // precision.
    template <typename dep_tracker_t>
    class null_ambient_context : public ambient_context_i<dep_tracker_t> {
    public:
        null_ambient_context(ast_manager& m, seq_util& u) : ambient_context_i<dep_tracker_t>(m, u) {}
        bool lower_bound(expr*, rational&, dep_tracker_t&) override { return false; }
        bool upper_bound(expr*, rational&, dep_tracker_t&) override { return false; }
        bool current_value(expr*, rational&) override { return false; }
        dep_tracker_t literal_if_false(expr*) override { return nullptr; }
        void add_diseq_axiom(expr*, expr*) override {}
    };

} // namespace seq
