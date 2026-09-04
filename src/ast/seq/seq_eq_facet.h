/*++
Copyright (c) 2026 Microsoft Corporation

Module Name:

    seq_eq_facet.h

Abstract:

    Sequence equality facet ("Phase 2" of the modular plugin-based search
    tree design, following the `stx::` core in util/stx_search_tree.h).

    This is the first concrete instantiation of the design document "A
    Modular Plugin-Based Search Tree for String Solving" (based on
    `theory_nseq` / `nielsen_graph` on the c3 branch): the `eq_facet`
    facet plus its propagation and split plugins, implementing classical
    word-equation solving via the Nielsen transformation directly over
    `expr_ref`/`seq_util`, with no dependency on `euf::sgraph`/`euf::snode`.

    A word equation `L = R` is represented as a pair of *token lists*: each
    side of a `str.++` chain is flattened into a vector of leaves, where a
    leaf is either
      - a length-1 string constant (a single character), or
      - an arbitrary non-constant term (treated as an opaque "variable" -
        it need not literally be a declared constant; any subterm the
        sequence theory has not otherwise decomposed is a valid Nielsen
        transformation atom).

    `eq_facet::propagate` performs the two deterministic, confluent parts of
    the transformation:
      - strip a common leading token off both sides (progress),
      - if one side becomes empty while the other is not, the nonempty side
        is *forced* to be empty: popping a leading variable is a forced
        (unconditional) substitution `v := epsilon`, while popping a leading
        constant is an immediate symbol-clash conflict.
      - if both sides reduce to empty, the equation is solved and removed.
      - if the leading tokens are two distinct constants, that is a symbol
        clash (conflict).

    `word_eq_split` performs the nondeterministic part: whenever some
    equation's leading tokens are a variable and a constant (in either
    order), or two distinct variables, it produces the classical Nielsen
    alternatives (`v := epsilon`, `v := c ++ v'`, or for two variables
    `v1 := epsilon`, `v2 := epsilon`, `v1 := v2 ++ v1'`) as sibling edges.

    Scope note: this facet alone is INCOMPLETE for word equations in
    general (e.g. `a ++ X = X ++ b` with `a != b` needs a length/periodicity
    argument to refute, which requires the arithmetic facet - a later
    phase); this module reproduces exactly the equational (Nielsen) part of
    `theory_nseq`, migrated per the design document's facet table (see
    z3papers/nseq/facet-eq-deq.md).

    "Phase 3" adds `deq_facet` (pending disequations `lhs != rhs`). Per
    the design (facet-eq-deq.md section 2.5), disequalities have no
    symmetric Nielsen branching of their own: `deq_facet` is a passive
    `subst_sink_i` that only reacts to substitutions broadcast from
    `eq_facet`'s split plugin (`word_eq_split`), discharging a
    disequation when prefix-stripping exposes distinct leading constants
    and flagging a conflict when both sides are forced fully equal.
    Without an `arith_facet` this is sound but incomplete (a disequation
    whose variables are never pinned down by `eq_facet`'s branching stays
    pending, contributing to "unknown" rather than a definite answer).

Author:

    Nikolaj Bjorner (nbjorner) 2026

--*/
#pragma once

#include "ast/ast.h"
#include "ast/seq_decl_plugin.h"
#include "ast/seq/seq_ambient_context.h"
#include "ast/rewriter/seq_rewriter.h"
#include "util/stx_search_tree.h"
#include "util/trail.h"

namespace seq {

    // Dependency source leaf type for this standalone (theory_nseq-free)
    // instantiation of the search tree: word-equation solving needs no
    // external SAT/EUF justification, so a plain unsigned tag (unused here,
    // but required by stx::search_tree's template parameter) suffices.
    using eq_tree = stx::search_tree<unsigned>;

    // A flattened side of a word equation is represented directly as an
    // `expr_ref_vector`: a sequence of tokens, each either a length-1
    // string constant or an opaque variable/term. Reference-counted
    // (rather than a raw ptr_vector<expr>) since tokens may be
    // freshly-created variables (e.g. from mk_fresh_var) that nothing
    // else in the system is holding a reference to.

    // Flatten a str-sort expr (a str.++ chain, possibly a bare leaf) into
    // its token list: constants are exploded into one token per character;
    // any other leaf (variable or otherwise-opaque term) becomes a single
    // token. `u` must be the seq_util of `e`'s ast_manager.
    void flatten(seq_util& u, expr* e, expr_ref_vector& out);

    // Is `e` a `seq.unit` wrapping a constant character?
    bool is_const_token(seq_util& u, expr* e);

    // Replace every occurrence of `var` in `ts` with the tokens of `repl`
    // (order-preserving splice). Shared helper between `eq_facet` and
    // `deq_facet` (and any future facet holding token-list equations).
    void subst_in(expr_ref_vector& ts, expr* var, expr_ref_vector const& repl);

    // Mixin implemented by any facet whose state is expressed over the
    // same shared variable pool as `eq_facet`'s token lists, so that a
    // substitution chosen by one facet's split plugin (e.g.
    // `word_eq_split`) is broadcast to every other such facet in the same
    // node - this is how `deq_facet` (and later `arith_facet`) stay in
    // sync with `eq_facet`'s Nielsen branching without needing their own
    // copy of the branching logic (see facet-eq-deq.md section 2.5: a
    // disequation is discharged/refuted only as a side effect of
    // substitutions driven by the equational system, never by inventing
    // its own).
    class subst_sink_i {
    public:
        virtual ~subst_sink_i() = default;
        // `subst_dep` is the dependency justifying the substitution
        // itself (e.g. the dependency of the equation whose branching
        // produced it). Each sink joins it (via its dep manager's
        // `mk_join`) with the existing dependency of every constraint it
        // actually mutates, so provenance accumulates through chains of
        // substitutions rather than being dropped.
        virtual void apply_subst(expr* var, expr_ref_vector const& repl, eq_tree::dep_tracker subst_dep) = 0;
    };

    // Trail undo object for a single-element `vector<T>::erase(idx)`:
    // remembers just the erased index and value (not the whole vector) and
    // re-inserts it at the same index on undo, restoring `erase`'s
    // shift-down with a shift-up. O(distance from idx to the end) at both
    // erase and undo time, versus the old whole-vector snapshot's O(n)
    // copy regardless of where the change was.
    template <typename T>
    class vector_erase_trail : public ::trail {
        vector<T>& m_vec;
        unsigned   m_idx;
        T          m_value;
    public:
        vector_erase_trail(vector<T>& v, unsigned idx) : m_vec(v), m_idx(idx), m_value(v[idx]) {}
        void undo() override {
            // Grow by one via a copy of m_value appended at the end (copy
            // *construction* is available even for move-only-assignable
            // T), then shift every element from idx..end-2 up by one
            // (move-assign, safe since no reallocation happens once the
            // vector has already grown), then drop m_value into the
            // now-vacant slot at m_idx.
            m_vec.push_back(m_value);
            for (unsigned i = m_vec.size() - 1; i > m_idx; --i)
                m_vec[i] = std::move(m_vec[i - 1]);
            m_vec[m_idx] = std::move(m_value);
        }
    };

    // Like value_trail<T>, but the target is a field of the idx'th element
    // of a vector, not a raw reference - so it stays safe even if later
    // operations (erase/push_back) reallocate or shift the vector's
    // storage before undo() runs. `Member` is a pointer-to-member selecting
    // the (move-only, e.g. expr_ref_vector/expr_ref) field to restore.
    template <typename Elem, typename T>
    class vector_field_trail : public ::trail {
        vector<Elem>& m_vec;
        unsigned      m_idx;
        T Elem::*     m_member;
        T             m_old_value;
    public:
        vector_field_trail(vector<Elem>& v, unsigned idx, T Elem::* member)
            : m_vec(v), m_idx(idx), m_member(member), m_old_value(v[idx].*member) {}
        void undo() override {
            m_vec[m_idx].*m_member = std::move(m_old_value);
        }
    };

    // Scan the field `ts` (the `member` field of the `idx`'th element of
    // `vec`) for `var`; if present, register a fine-grained undo (just
    // this one field, addressed by vector+index+member so it stays valid
    // across later vector reallocation - not the whole facet's
    // equation/disequation/membership/ncontains vector) and perform the
    // substitution, returning true. If `var` does not occur, this is a
    // no-op returning false: apply_subst's per-call loop over every entry
    // only pays for a trail object on the entries that actually change.
    template <typename Elem>
    inline bool subst_in_trailed(trail_stack& trail, vector<Elem>& vec, unsigned idx, expr_ref_vector Elem::* member, expr* var, expr_ref_vector const& repl) {
        expr_ref_vector& ts = vec[idx].*member;
        bool present = false;
        for (expr* t : ts)
            if (t == var) { present = true; break; }
        if (!present)
            return false;
        trail.push(vector_field_trail<Elem, expr_ref_vector>(vec, idx, member));
        subst_in(ts, var, repl);
        return true;
    }

    /**
     * Facet holding a set of pending word equations. Equations are
     * discharged (removed) as soon as they are solved; the facet is
     * satisfied when the set is empty.
     */
    class eq_facet : public stx::facet_i, public subst_sink_i {
    public:
        struct equation {
            expr_ref_vector      m_lhs;
            expr_ref_vector      m_rhs;
            // Justification for this equation: for a root-level equation,
            // the dependency of the original assertion it came from
            // (nullptr/empty if none); for an equation produced by
            // simplification (reduce_eq's sub-equations), the parent
            // equation's dependency (the decomposition is definitional,
            // not an added assumption, so no new leaf is introduced).
            eq_tree::dep_tracker m_dep;
            equation(expr_ref_vector const& lhs, expr_ref_vector const& rhs, eq_tree::dep_tracker dep = nullptr) :
                m_lhs(lhs), m_rhs(rhs), m_dep(dep) {}
            bool operator<(equation const& other) const;
            bool operator==(equation const& other) const;
        };

    private:
        ast_manager&          m;
        seq_util&             u;
        seq_rewriter          m_rw;
        eq_tree::dep_manager_t& m_dm;
        vector<equation>      m_eqs;

    public:
        eq_facet(trail_stack& trail, ast_manager& m, seq_util& u, eq_tree::dep_manager_t& dm) :
            facet_i(trail), m(m), u(u), m_rw(m), m_dm(dm) {}

        ast_manager& get_manager() const { return m; }
        seq_util& get_seq_util() const { return u; }
        eq_tree::dep_manager_t& dm() const { return m_dm; }

        // Non-trailed: only for root construction, before any search has
        // begun (no branch to undo back past).
        void add_equation(expr_ref_vector const& lhs, expr_ref_vector const& rhs, eq_tree::dep_tracker dep = nullptr) {
            m_eqs.push_back(equation(lhs, rhs, dep));
        }
        void add_equation(expr* lhs, expr* rhs, eq_tree::dep_tracker dep = nullptr) {
            expr_ref_vector lts(m), rts(m);
            flatten(u, lhs, lts);
            flatten(u, rhs, rts);
            add_equation(lts, rts, dep);
        }

        // Trailed variant: for adding a new equation to an existing
        // branch mid-search (e.g. ncontains_split's "needle aligns here"
        // branch, which introduces a fresh eq_facet equation rather than
        // a substitution). Undo just pops the pushed element.
        void add_equation_trailed(expr_ref_vector const& lhs, expr_ref_vector const& rhs, eq_tree::dep_tracker dep = nullptr) {
            m_eqs.push_back(equation(lhs, rhs, dep));
            m_trail.push(push_back_trail<equation>(m_eqs));
        }

        // Trailed removal of the equation at `idx` (e.g. eq_split
        // replacing one equation with two shorter ones): uses
        // vector_erase_trail so the removed element is restored at the
        // same index on undo, regardless of any push_back_trailed
        // insertions that may have shifted the vector's storage since.
        void remove_equation_trailed(unsigned idx) {
            m_trail.push(vector_erase_trail<equation>(m_eqs, idx));
            m_eqs.erase(m_eqs.begin() + idx);
        }

        vector<equation> const& equations() const { return m_eqs; }

        // Apply a forced/branch substitution `var := repl` to every
        // equation currently in the facet. Trailed per-equation: only
        // equations that actually contain `var` register an undo object
        // (see subst_in_trailed). Each touched equation's dependency is
        // joined with `subst_dep` (the justification for the
        // substitution itself), also trailed.
        // Allocate a fresh opaque variable token of `s`'s sort.
        expr* mk_fresh_var(sort* s) { return m.mk_fresh_const("t", s); }

        // -- stx::facet_i --
        facet_i* clone(trail_stack& trail) const override;
        unsigned hash() const override;
        bool similar(facet_i const& other) const override;
        bool is_satisfied() const override { return m_eqs.empty(); }

        // Deterministic simplification pass: uses seq_rewriter::reduce_eq
        // to simplify each equation's token lists (prefix/suffix
        // stripping, unit-vs-unit decomposition, symbol-clash and other
        // contradiction detection, length-based reasoning, etc.), removes
        // solved (both-empty) equations, and folds any newly-produced
        // sub-equations back into the set. Returns true if the equation
        // set changed (informational only - the engine detects the fixed
        // point itself via facet hashing). Trailed. On conflict, sets
        // `conflict_dep` to the dependency of the equation that produced
        // the contradiction. See module comment.
        bool simplify(bool& conflict, eq_tree::dep_tracker& conflict_dep);
        ambient_context_i<eq_tree::dep_tracker> const& ambient(eq_tree::node const& n) const;

    private:
        void apply_subst(expr* var, expr_ref_vector const& repl, eq_tree::dep_tracker subst_dep) override;
        // Simplify a single equation (by index into m_eqs) using
        // seq_rewriter::reduce_eq. Returns false and sets conflict=true
        // (and conflict_dep to the culprit equation's dependency) if the
        // equation is contradictory; otherwise returns true. Sets
        // changed=true if the equation's token lists were mutated or new
        // sub-equations were appended to m_eqs. On success, if both sides
        // reduced to empty, the equation is erased (trailed).
        bool simplify_equation(unsigned idx, bool& conflict, eq_tree::dep_tracker& conflict_dep, bool& changed);
        friend void broadcast_subst(eq_tree::node& target, stx::facet_id eq_id, expr* var, expr_ref_vector const& repl, eq_tree::dep_tracker subst_dep);
    };

    void broadcast_subst(eq_tree::node& target, stx::facet_id eq_id, expr* var, expr_ref_vector const& repl, eq_tree::dep_tracker subst_dep);

    // Deterministic propagation plugin wrapping eq_facet::simplify.
    class eq_propagation : public eq_tree::propagation_plugin_i {
        stx::facet_id m_id;
    public:
        explicit eq_propagation(stx::facet_id id) : m_id(id) {}
        char const* name() const override { return "eq-propagate"; }
        stx::simplify_result propagate(eq_tree::node& n) override;
    };

    // Nielsen-transformation split plugin: branches the first equation
    // whose leading OR trailing tokens are not both resolved by
    // propagation (i.e. a variable paired with a constant, or two
    // distinct variables) - mirroring the c3 branch's `apply_const_nielsen`/
    // `apply_var_nielsen`, each of which loops over both directions
    // (`od` in {0=forward/prefix, 1=backward/suffix}) so that a trailing
    // clash (e.g. `x ++ a = y ++ b`) is caught exactly like a leading one
    // (`eq_propagation`/`reduce_eq`'s own `reduce_back`/`reduce_front`
    // pair already strips agreeing prefixes/suffixes deterministically;
    // this split plugin is the nondeterministic counterpart, so it must
    // examine both ends too - a leading-only check would miss branching
    // opportunities exposed only at the tail, e.g. after a suffix
    // narrowed by some other facet's substitution). The first branch is
    // materialized immediately by `split()`; remaining branches (up to
    // two more, for the two-variable case) are produced lazily by the
    // returned `split_iterator_i` on resumption.
    class word_eq_split : public eq_tree::split_plugin_i {
        ast_manager& m;
        seq_util&    u;
        stx::facet_id m_id;

        class iterator : public eq_tree::split_iterator_i {
            eq_tree::node& m_n;
            stx::facet_id  m_id;
            // Remaining alternatives to produce, in order. Each entry is a
            // (rule_name, var, replacement, dep) tuple - `m_dep` is the
            // dependency of the equation whose stuck leading/trailing
            // tokens motivated this split (a case-split on how to unstick
            // a single equation derives its justification from that one
            // equation, not a join of several). `next()` pops the front
            // one, mutates in place, pushes a scope, and returns it. The
            // replacement vector is already built in the correct
            // direction by `split()` (`[c, v']` for a forward/prefix
            // branch, `[v', c]` for a backward/suffix branch), so
            // `next()` itself does not need to know which direction
            // produced it.
            struct alt { char const* m_name; expr* m_var; expr_ref_vector m_repl; eq_tree::dep_tracker m_dep; };
            vector<alt>    m_pending;
            unsigned       m_pos = 0;
        public:
            iterator(eq_tree::node& n, stx::facet_id id) : m_n(n), m_id(id) {}
            void push_back(char const* name, expr* var, expr_ref_vector const& repl, eq_tree::dep_tracker dep) {
                m_pending.push_back(alt{ name, var, repl, dep });
            }
            bool next(eq_tree::edge& out) override;
        };

    public:
        word_eq_split(ast_manager& m, seq_util& u, stx::facet_id id) : m(m), u(u), m_id(id) {}
        char const* name() const override { return "nielsen-split"; }
        scoped_ptr<eq_tree::split_iterator_i> split(eq_tree::node& n, unsigned cost, eq_tree::edge& out, bool& has_more, bool& committed) override;
    };

    // Mid-equation split with a padding variable, ported from the c3
    // branch's `apply_eq_split`/`find_eq_split_point`
    // (seq_nielsen_modifiers.cpp) per facet-eq-deq.md section 2.2. Unlike
    // `word_eq_split` (which only ever peels the *head* token of an
    // equation), this rule looks for an interior position on each side
    // where the multiset of variable tokens consumed so far balances out
    // between LHS and RHS - at such a position the two prefixes must have
    // equal length up to a constant offset ("padding"), so the equation
    // can be safely cut in two there, each half strictly shorter than the
    // original (bounding recursion) without losing any solutions: this is
    // a single deterministic *progress* transformation, not a
    // multi-branch case split, so it is offered at split cost 0 exactly
    // like word_eq_split, but always commits its lone alternative
    // immediately (no resumable iterator, mirroring power_split's
    // single-branch cases).
    //
    // If lhs is longer than rhs at the split (padding > 0), a fresh
    // Skolem "pad" variable is introduced and spliced onto the shorter
    // (rhs) side at the split point (mirrored if rhs is longer); an
    // exact-length constraint `len(pad) = |padding|` plus the two new
    // equations' own `len(lhs)=len(rhs)` constraints are asserted into
    // arith_facet, all tagged with the original equation's dependency.
    class eq_split : public eq_tree::split_plugin_i {
        ast_manager&  m;
        seq_util&     u;
        stx::facet_id m_eq_id;
        stx::facet_id m_arith_id;

        // Classify a token's length as a known constant (chars, always 1
        // here since flatten() explodes multi-char strings into
        // single-char tokens) or unknown/variable (anything else,
        // including fresh Skolem/opaque terms).
        static bool token_has_variable_length(seq_util& u, expr* tok) { return !is_const_token(u, tok); }

    public:
        eq_split(ast_manager& m, seq_util& u, stx::facet_id eq_id, stx::facet_id arith_id) :
            m(m), u(u), m_eq_id(eq_id), m_arith_id(arith_id) {}
        char const* name() const override { return "eq-split"; }

        // Walk `lhs`/`rhs` token lists looking for a balanced interior
        // split point, as in the c3 branch's find_eq_split_point (see
        // module comment above and the .cpp implementation for the
        // per-token signed-balance algorithm and its history). Returns
        // false if no such point exists.
        static bool find_eq_split_point(seq_util& u, expr_ref_vector const& lhs, expr_ref_vector const& rhs,
                                         unsigned& out_lhs_idx, unsigned& out_rhs_idx, int& out_padding);

        scoped_ptr<eq_tree::split_iterator_i> split(eq_tree::node& n, unsigned cost, eq_tree::edge& out, bool& has_more, bool& committed) override;
    };

    // `ite` token split (eq, arith): per the token model (README.md
    // section 5.1.1 / ambient_context_i::is_var above), a `m.is_ite(x)`
    // token is neither a unit nor a power but is ALSO not treated as a
    // freely-substitutable Nielsen variable (is_var excludes it
    // explicitly) - it is a case split on its own condition, not on its
    // relationship to another token. This rule finds the first `ite`
    // token `(ite c t1 t2)` occurring in any pending equation and
    // branches:
    //   1. assert `c` as a hypothesis on arith_facet's sub-solver (via
    //      add_constraint, dependency-tracked to the equation's own dep)
    //      and substitute the token by `flatten(t1)`,
    //   2. assert `!c` likewise and substitute by `flatten(t2)`.
    // Both `c` and `!c` are asserted (never simultaneously live - each
    // is scoped to its own branch by the driver's trail push/pop) purely
    // as a dependency-tracked fact of the incremental arithmetic backend,
    // exactly like `apply_power_epsilon`'s disjunction branch
    // (facet-eq-deq.md section 2.3) - this is what lets `arith_facet`'s
    // `unsat_core()`/`conflict_dep()` surface `c`'s hypothesis as the
    // culprit dependency of a branch that turns out infeasible. The
    // caller embedding this tree in a live SMT context (`theory_nseq`)
    // is expected to recognize a hypothesis dependency of this shape
    // (originating from an `ite` condition, as opposed to an ordinary
    // equation-derived dependency) via its own dependency-to-literal
    // translation layer (mirroring `theory_seq::assumption`/
    // `deps_to_lits`) and surface `c` as a literal it may branch on
    // directly in the ambient SAT search, rather than only ever seeing
    // it folded anonymously into an unsat core.
    class ite_split : public eq_tree::split_plugin_i {
        ast_manager&  m;
        seq_util&     u;
        stx::facet_id m_eq_id;
        stx::facet_id m_arith_id;

        // Remaining alternative (branch 2, `!c`) after branch 1 (`c`) is
        // materialized immediately by `split()`.
        class iterator : public eq_tree::split_iterator_i {
            eq_tree::node& m_n;
            stx::facet_id  m_eq_id;
            stx::facet_id  m_arith_id;
            expr_ref       m_tok, m_cond;
            expr_ref_vector m_repl2;
            eq_tree::dep_tracker m_dep;
            bool           m_done = false;
            ast_manager&   m;
        public:
            iterator(eq_tree::node& n, stx::facet_id eq_id, stx::facet_id arith_id,
                      expr* tok, expr* cond, expr_ref_vector const& repl2, eq_tree::dep_tracker dep, ast_manager& m) :
                m_n(n), m_eq_id(eq_id), m_arith_id(arith_id), m_tok(tok, m), m_cond(cond, m), m_repl2(repl2), m_dep(dep), m(m) {}
            bool next(eq_tree::edge& out) override;
        };

    public:
        ite_split(ast_manager& m, seq_util& u, stx::facet_id eq_id, stx::facet_id arith_id) :
            m(m), u(u), m_eq_id(eq_id), m_arith_id(arith_id) {}
        char const* name() const override { return "ite-split"; }
        scoped_ptr<eq_tree::split_iterator_i> split(eq_tree::node& n, unsigned cost, eq_tree::edge& out, bool& has_more, bool& committed) override;
    };

    /**
     * Facet holding a set of pending word disequations (`lhs != rhs`).
     * Per the design (z3papers/nseq/facet-eq-deq.md section 2.5),
     * `deq_facet` has no Nielsen branching of its own: it only reacts,
     * via `subst_sink_i::apply_subst`, to substitutions chosen by
     * `eq_facet`'s split plugin (`word_eq_split`, broadcast via
     * `subst_sink_i`). A disequation is discharged (removed, i.e. proved
     * satisfiable-distinct) as soon as prefix-stripping exposes two
     * distinct leading constants; it is a conflict if prefix-stripping
     * reduces both sides to empty (the two sides were forced equal,
     * contradicting `!=`). Otherwise it is left pending (sound but
     * incomplete without an arith_facet - see module comment).
     */
    class deq_facet : public stx::facet_i, public subst_sink_i {
    public:
        struct disequation {
            expr_ref_vector      m_lhs;
            expr_ref_vector      m_rhs;
            eq_tree::dep_tracker m_dep;
            disequation(expr_ref_vector const& lhs, expr_ref_vector const& rhs, eq_tree::dep_tracker dep = nullptr) :
                m_lhs(lhs), m_rhs(rhs), m_dep(dep) {}
            bool operator<(disequation const& other) const;
            bool operator==(disequation const& other) const;
        };

    private:
        ast_manager& m;
        seq_util&    u;
        eq_tree::dep_manager_t& m_dm;
        vector<disequation> m_diseqs;

    public:
        deq_facet(trail_stack& trail, ast_manager& m, seq_util& u, eq_tree::dep_manager_t& dm) :
            facet_i(trail), m(m), u(u), m_dm(dm) {}

        ast_manager& get_manager() const { return m; }
        seq_util& get_seq_util() const { return u; }

        // Non-trailed: root construction only.
        void add_disequation(expr_ref_vector const& lhs, expr_ref_vector const& rhs, eq_tree::dep_tracker dep = nullptr) {
            m_diseqs.push_back(disequation(lhs, rhs, dep));
        }
        void add_disequation(expr* lhs, expr* rhs, eq_tree::dep_tracker dep = nullptr) {
            expr_ref_vector lts(m), rts(m);
            flatten(u, lhs, lts);
            flatten(u, rhs, rts);
            add_disequation(lts, rts, dep);
        }

        vector<disequation> const& disequations() const { return m_diseqs; }

        // Apply a substitution `var := repl` (chosen elsewhere, by
        // eq_facet's split plugin) to every pending disequation. Trailed
        // per-disequation (only entries containing `var` register undo).
        // The touched disequation's dependency is joined with
        // `subst_dep`, also trailed.
        void apply_subst(expr* var, expr_ref_vector const& repl, eq_tree::dep_tracker subst_dep) override;

        // Trailed variant of add_disequation, for use mid-search (e.g.
        // deq_split's equal-length branch, which introduces a fresh,
        // more precise single-character disequation `a != b` alongside
        // discharging the original). Undo just pops the pushed element.
        void add_disequation_trailed(expr_ref_vector const& lhs, expr_ref_vector const& rhs, eq_tree::dep_tracker dep = nullptr) {
            m_diseqs.push_back(disequation(lhs, rhs, dep));
            m_trail.push(push_back_trail<disequation>(m_diseqs));
        }

        // Trailed removal of the disequation at `idx` (e.g. deq_split
        // discharging/replacing a stuck disequation): uses
        // vector_erase_trail so the removed element is restored at the
        // same index on undo.
        void remove_disequation_trailed(unsigned idx) {
            m_trail.push(vector_erase_trail<disequation>(m_diseqs, idx));
            m_diseqs.erase(m_diseqs.begin() + idx);
        }

        // -- stx::facet_i --
        facet_i* clone(trail_stack& trail) const override;
        unsigned hash() const override;
        bool similar(facet_i const& other) const override;
        bool is_satisfied() const override { return m_diseqs.empty(); }

        // Deterministic simplification pass: prefix-stripping, then
        // discharge-on-symbol-clash / conflict-on-both-empty. On
        // conflict, sets `conflict_dep` to the culprit disequation's
        // dependency. See module comment. Trailed.
        bool simplify(bool& conflict, eq_tree::dep_tracker& conflict_dep);
    };

    // Deterministic propagation plugin wrapping deq_facet::simplify.
    class deq_propagation : public eq_tree::propagation_plugin_i {
        stx::facet_id m_id;
    public:
        explicit deq_propagation(stx::facet_id id) : m_id(id) {}
        char const* name() const override { return "deq-propagate"; }
        stx::simplify_result propagate(eq_tree::node& n) override;
    };

    // Disequation case-split, ported from the c3 branch's
    // `axiomatize_diseq` (seq_nielsen_modifiers.cpp) per
    // facet-eq-deq.md section 2.5. Unlike equalities, disequalities have
    // no symmetric Nielsen-modifier family: `deq_facet::simplify` only
    // ever discharges a disequation once prefix-stripping exposes two
    // distinct leading constants, or detects a conflict once both sides
    // are forced identical - it never invents a substitution of its own.
    // Without this rule a disequation stuck behind two distinct
    // variables (e.g. `x . a != y . b`) can never be resolved, since no
    // other plugin ever mutates deq_facet's pending set except via
    // subst_sink_i::apply_subst broadcasts triggered by *eq_facet's* own
    // splits.
    //
    // For a stuck disequation `u != v` (both sides nonempty, and not
    // already resolved by simplification), branches into exactly 3
    // cases, spanning deq_facet + eq_facet + arith_facet:
    //   1. `len(u) < len(v)` (arith-only; a length mismatch alone
    //      already proves `u != v`, so the disequation is discharged -
    //      removed from deq_facet - in this branch).
    //   2. `len(v) < len(u)` (symmetric).
    //   3. equal-length split: fresh skolem terms `w` (common prefix,
    //      same sort as u/v), `a`, `b` (fresh single-char unit terms),
    //      `u'`, `v'` (fresh suffix vars); asserts new eq_facet equations
    //      `u = w.a.u'` and `v = w.b.v'`, an arith_facet constraint
    //      `len(u') = len(v')`, and replaces the original disequation
    //      with the finer-grained `a != b` (a single-token disequation
    //      between two fresh unit chars) - this is what actually proves
    //      `u != v` in this branch, given the two new equalities.
    // All three branches are justified solely by the disequation's own
    // dependency (a case-split on how to resolve one stuck disequation).
    class deq_split : public eq_tree::split_plugin_i {
        ast_manager&  m;
        seq_util&     u;
        stx::facet_id m_deq_id;
        stx::facet_id m_eq_id;
        stx::facet_id m_arith_id;

        // Remaining alternatives (case 2, then case 3) after case 1 (if
        // offered) is the first, immediately materialized branch -
        // mirrors word_eq_split::iterator's "alt" list pattern.
        class iterator : public eq_tree::split_iterator_i {
            eq_tree::node& m_n;
            stx::facet_id  m_deq_id;
            stx::facet_id  m_eq_id;
            stx::facet_id  m_arith_id;
            unsigned       m_diseq_idx;
            expr_ref_vector m_lhs, m_rhs; // the original disequation's sides, captured before any branch mutates the vector
            eq_tree::dep_tracker m_dep;
            unsigned       m_next_case; // 2, then 3, then done
            ast_manager&   m;
            seq_util&      u;
        public:
            iterator(eq_tree::node& n, stx::facet_id deq_id, stx::facet_id eq_id, stx::facet_id arith_id,
                      unsigned diseq_idx, expr_ref_vector const& lhs, expr_ref_vector const& rhs,
                      eq_tree::dep_tracker dep, unsigned next_case, ast_manager& m, seq_util& u) :
                m_n(n), m_deq_id(deq_id), m_eq_id(eq_id), m_arith_id(arith_id),
                m_diseq_idx(diseq_idx), m_lhs(lhs), m_rhs(rhs), m_dep(dep), m_next_case(next_case), m(m), u(u) {}
            bool next(eq_tree::edge& out) override;
        };

    public:
        deq_split(ast_manager& m, seq_util& u, stx::facet_id deq_id, stx::facet_id eq_id, stx::facet_id arith_id) :
            m(m), u(u), m_deq_id(deq_id), m_eq_id(eq_id), m_arith_id(arith_id) {}
        char const* name() const override { return "deq-split"; }
        scoped_ptr<eq_tree::split_iterator_i> split(eq_tree::node& n, unsigned cost, eq_tree::edge& out, bool& has_more, bool& committed) override;
    };

} // namespace seq
