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
        `snode` at all - see seq_eq_facet.h's module comment). Any
        plugin/facet that needs to distinguish an opaque *solvable
        variable* token (something the Nielsen/arithmetic engine may
        freely substitute) from an *interpreted* term it must leave
        alone (a concat, string literal, unit, itos, nth, map/mapi/
        foldl/foldli application, ite, etc.) should call
        `ambient_context_i::is_var` rather than reinventing the predicate
        locally. The concrete implementation living under `src/smt`
        should simply forward to `theory_seq::is_var` (`theory_seq.h/
        .cpp`, itself a thin wrapper - `theory_seq::is_var` just calls
        `m_eq.is_var`, `eq_solver::is_var` in
        ast/seq/seq_eq_solver.cpp) so that the ambient-context notion of
        "variable" is always exactly what `theory_seq`'s own equation
        solver already uses - not a second, possibly-diverging copy of
        the predicate. `is_solvable_var` below (used by the context-free
        `null_ambient_context` fallback, e.g. in unit tests with no live
        `theory_seq` wired up) is kept textually identical to
        `eq_solver::is_var` for exactly this reason.

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
    public:
        ~ambient_context_i() override = default;

        // Is `e` an opaque, freely-substitutable "variable" token (as
        // opposed to an interpreted/structured term such as a
        // concatenation, string literal, unit, itos, nth, map/mapi/
        // foldl/foldli application, or ite) - i.e. is it safe for a split
        // plugin (word_eq_split, power_split, etc.) to treat `e` as a
        // Nielsen-transformation variable and substitute it wholesale?
        // Replaces the c3 branch's `euf::snode::is_var()`.
        virtual bool is_var(expr* e) const = 0;

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

    // Reference predicate for `ambient_context_i::is_var`, shared so that
    // every concrete implementation (and any facet that must fall back to
    // a context-free check, e.g. in a unit test with no ambient context
    // wired up) agrees on the same notion of "opaque variable" as
    // `eq_solver::is_var` (ast/seq/seq_eq_solver.cpp) - the two must never
    // silently diverge, since `word_eq_split`'s `is_const_token`-based
    // dichotomy (ast/seq/seq_eq_facet.cpp) implicitly assumes "not a
    // const token" already coincides with this predicate.
    inline bool is_solvable_var(ast_manager& m, seq_util& u, expr* e) {
        return
            u.is_seq(e->get_sort()) &&
            !u.str.is_concat(e) &&
            !u.str.is_empty(e) &&
            !u.str.is_string(e) &&
            !u.str.is_unit(e) &&
            !u.str.is_itos(e) &&
            !u.str.is_nth_i(e) &&
            !u.str.is_map(e) &&
            !u.str.is_mapi(e) &&
            !u.str.is_foldl(e) &&
            !u.str.is_foldli(e) &&
            !m.is_ite(e);
    }

    // Trivial, always-"unknown" implementation: usable by unit tests (or
    // any facet standing alone with no live ambient SMT context) that
    // only need `is_var` (delegated to `is_solvable_var`) and can safely
    // treat every bound/value query as "not currently known" - never
    // reports a false bound, only ever a possible loss of precision.
    template <typename dep_tracker_t>
    class null_ambient_context : public ambient_context_i<dep_tracker_t> {
        ast_manager& m;
        seq_util&    u;
    public:
        null_ambient_context(ast_manager& m, seq_util& u) : m(m), u(u) {}
        bool is_var(expr* e) const override { return is_solvable_var(m, u, e); }
        bool lower_bound(expr*, rational&, dep_tracker_t&) override { return false; }
        bool upper_bound(expr*, rational&, dep_tracker_t&) override { return false; }
        bool current_value(expr*, rational&) override { return false; }
        dep_tracker_t literal_if_false(expr*) override { return nullptr; }
        void add_diseq_axiom(expr*, expr*) override {}
    };

} // namespace seq
