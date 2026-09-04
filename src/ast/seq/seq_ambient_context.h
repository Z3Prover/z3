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
        dependencies today (`seq_solver_facet.cpp`).
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

    // Forward declarations only - this header must stay free of any
    // dependency on the concrete facet classes (see module comment
    // above); `ambient_context_i`'s typed accessor methods below
    // (`eq_facet`, `mem_facet`, ...) are member function templates on
    // the node type, so each is only instantiated (and so only requires
    // its facet type to be complete) at the point it is actually called
    // - i.e. in whichever .cpp already includes the concrete facet
    // header - not here.
    class eq_facet;
    class deq_facet;
    class power_facet;
    class mem_facet;
    class ncontains_facet;
    class solver_facet_i;

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

        // Sentinel for "not (yet) registered" - distinct from any real
        // facet_id (facet_id 0 is a legitimate id, so it cannot double as
        // "unset").
        static constexpr stx::facet_id no_facet = ~0u;

        // Sibling facet ids, collected here once (by whoever assembles
        // the search tree - a test fixture today, `theory_nseq`
        // eventually) right after the corresponding `register_facet<...>`
        // calls, via the setters below. Every propagation/split plugin
        // that used to take these as constructor arguments now instead
        // reads them off `node::ambient()` (cast down to this type) at
        // the point of use (`propagate(node&)`/`split(node&, ...)`), so
        // that assembling a new combination of facets/plugins for a node
        // no longer requires threading each sibling's id through every
        // plugin constructor - it only requires registering the ids here
        // once.
        stx::facet_id m_eq_id = no_facet;
        stx::facet_id m_deq_id = no_facet;
        stx::facet_id m_arith_id = no_facet;
        stx::facet_id m_pow_id = no_facet;
        stx::facet_id m_mem_id = no_facet;
        stx::facet_id m_ncontains_id = no_facet;

        // Raw facet ids are deliberately not public: nothing outside this
        // class (or the facet-accessor templates just below, which are
        // the only legitimate consumers) should need a bare `facet_id` -
        // every caller that used to write `n.facet_as<mem_facet>(ac.
        // mem_id())` should instead write `ac.mem_facet(n)` and never see
        // an id at all. `broadcast_subst` (seq_eq_facet.h/.cpp) no longer
        // needs any of these either - it distinguishes the eq_facet it
        // already updated directly from every other sibling facet by
        // pointer identity, not by id.
        stx::facet_id eq_id() const { return m_eq_id; }
        stx::facet_id deq_id() const { return m_deq_id; }
        stx::facet_id arith_id() const { return m_arith_id; }
        stx::facet_id pow_id() const { return m_pow_id; }
        stx::facet_id mem_id() const { return m_mem_id; }
        stx::facet_id ncontains_id() const { return m_ncontains_id; }
    public:
        ambient_context_i(ast_manager& m, seq_util& u) : m(m), u(u) {}
        ~ambient_context_i() override = default;

        void set_eq_id(stx::facet_id id) { m_eq_id = id; }
        void set_deq_id(stx::facet_id id) { m_deq_id = id; }
        void set_arith_id(stx::facet_id id) { m_arith_id = id; }
        void set_pow_id(stx::facet_id id) { m_pow_id = id; }
        void set_mem_id(stx::facet_id id) { m_mem_id = id; }
        void set_ncontains_id(stx::facet_id id) { m_ncontains_id = id; }

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

        // Retrieve one of this node's sibling facets directly, coercing
        // it to its concrete type in one call - e.g. `ac.mem_facet(n)`
        // instead of the old two-step `n.facet_as<mem_facet>(ac.mem_id())`.
        // `node_t` is a template parameter (rather than a fixed
        // `stx::search_tree<...>::node`) purely so this header does not
        // need to name any one `search_tree` instantiation; every current
        // caller passes `eq_tree::node` (see seq_eq_facet.h). Each method
        // is a member function template, so (like `facet_as<T>` itself)
        // it is only instantiated - and so only requires its facet type
        // to be complete - at the point it is actually called, i.e. in
        // whichever .cpp already `#include`s that facet's own header.
        template <typename node_t> seq::eq_facet& eq_facet(node_t& n) const { return n.template facet_as<seq::eq_facet>(eq_id()); }
        template <typename node_t> seq::deq_facet& deq_facet(node_t& n) const { return n.template facet_as<seq::deq_facet>(deq_id()); }
        template <typename node_t> seq::power_facet& power_facet(node_t& n) const { return n.template facet_as<seq::power_facet>(pow_id()); }
        template <typename node_t> seq::mem_facet& mem_facet(node_t& n) const { return n.template facet_as<seq::mem_facet>(mem_id()); }
        template <typename node_t> seq::ncontains_facet& ncontains_facet(node_t& n) const { return n.template facet_as<seq::ncontains_facet>(ncontains_id()); }
        template <typename node_t> seq::solver_facet_i& arith_facet(node_t& n) const { return n.template facet_as<seq::solver_facet_i>(arith_id()); }

        template <typename node_t> bool has_eq(node_t& n) const { return n.has_facet(eq_id()); }
        template <typename node_t> bool has_deq(node_t& n) const { return n.has_facet(deq_id()); }
        template <typename node_t> bool has_power(node_t& n) const { return n.has_facet(pow_id()); }
        template <typename node_t> bool has_mem(node_t& n) const { return n.has_facet(mem_id()); }
        template <typename node_t> bool has_ncontains(node_t& n) const { return n.has_facet(ncontains_id()); }
        template <typename node_t> bool has_arith(node_t& n) const { return n.has_facet(arith_id()); }
    };

    /**
     * A lightweight, non-owning proxy bundling a search-tree node
     * together with its ambient context, so a call site can write
     * `get_ambient(n).mem_facet()` instead of the old two-step
     * `n.facet_as<mem_facet>(get_ambient(n).mem_id())`. The ambient context already knows every sibling's `facet_id`
     * (`eq_id()`, `mem_id()`, etc.); this class just adds the missing
     * piece - the node to call `facet_as<T>` on - and one accessor
     * method per sibling facet type.
     *
     * Since this is itself a class template, a method such as
     * `mem_facet()` is only instantiated (and so only requires `seq::
     * mem_facet` to be a complete type) at the point it is actually
     * called - i.e. in whichever .cpp already `#include`s the concrete
     * facet's header. `seq_ambient_context.h` itself never needs to see
     * those headers, only the forward declarations above; this is what
     * lets `ambient_ref` return real reference types (`mem_facet&`, not
     * `facet_i&` requiring a further cast at every call site) without
     * creating a header dependency cycle.
     */
    template <typename node_t, typename dep_tracker_t>
    class ambient_ref {
        node_t& m_node;
        ambient_context_i<dep_tracker_t>& m_ac;
    public:
        ambient_ref(node_t& n, ambient_context_i<dep_tracker_t>& ac) : m_node(n), m_ac(ac) {}

        // Access to the underlying context (bounds/values queries,
        // is_var, ...) for call sites that still need those directly.
        // Note: raw facet ids are intentionally not exposed here - use
        // the typed accessors (eq_facet_ref(), etc.) or has_eq()/etc.
        ambient_context_i<dep_tracker_t>& context() const { return m_ac; }
        node_t& node() const { return m_node; }

        bool is_var(expr* e) const { return m_ac.is_var(e); }
        bool lower_bound(expr* e, rational& lo, dep_tracker_t& dep) const { return m_ac.lower_bound(e, lo, dep); }
        bool upper_bound(expr* e, rational& hi, dep_tracker_t& dep) const { return m_ac.upper_bound(e, hi, dep); }
        bool current_value(expr* e, rational& v) const { return m_ac.current_value(e, v); }
        dep_tracker_t literal_if_false(expr* e) const { return m_ac.literal_if_false(e); }
        void add_diseq_axiom(expr* e1, expr* e2) const { m_ac.add_diseq_axiom(e1, e2); }

        eq_facet& eq_facet_ref() const { return m_ac.eq_facet(m_node); }
        deq_facet& deq_facet_ref() const { return m_ac.deq_facet(m_node); }
        power_facet& power_facet_ref() const { return m_ac.power_facet(m_node); }
        mem_facet& mem_facet_ref() const { return m_ac.mem_facet(m_node); }
        ncontains_facet& ncontains_facet_ref() const { return m_ac.ncontains_facet(m_node); }
        solver_facet_i& arith_facet_ref() const { return m_ac.arith_facet(m_node); }

        bool has_eq() const { return m_ac.has_eq(m_node); }
        bool has_deq() const { return m_ac.has_deq(m_node); }
        bool has_power() const { return m_ac.has_power(m_node); }
        bool has_mem() const { return m_ac.has_mem(m_node); }
        bool has_ncontains() const { return m_ac.has_ncontains(m_node); }
        bool has_arith() const { return m_ac.has_arith(m_node); }
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
