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
    Clemens Eisenhofer 2026
    Margus Veanes 2026

--*/
#pragma once

#include "ast/ast.h"
#include "ast/seq_decl_plugin.h"
#include "ast/seq/seq_ambient_context.h"
#include "ast/rewriter/seq_rewriter.h"
#include "ast/seq/seq_eq_approx.h"
#include "util/stx_search_tree.h"
#include "util/trail.h"
#include <algorithm>

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

    // Tokens are obtained directly via `u.str.get_concat_units(e, out)`:
    // constants are exploded into one token per character; any other
    // leaf (variable or otherwise-opaque term) becomes a single token.

    // Lexicographic comparison of two token vectors by ast id (shorter
    // vector sorts first on a length mismatch, then compared elementwise).
    // Shared by eq_facet's equation/disequation, ncontains_facet's
    // str_ncontains, and mem_facet's str_mem operator< implementations.
    inline int cmp_tokens(expr_ref_vector const& a, expr_ref_vector const& b) {
        unsigned n = std::min(a.size(), b.size());
        for (unsigned i = 0; i < n; ++i) {
            unsigned ida = a[i]->get_id(), idb = b[i]->get_id();
            if (ida != idb)
                return ida < idb ? -1 : 1;
        }
        if (a.size() != b.size())
            return a.size() < b.size() ? -1 : 1;
        return 0;
    }

    // Recover the node's ambient context, bundled together with the node
    // itself into an `ambient_ref`, so that a propagation/split plugin
    // can coerce straight to a sibling facet's own type in one call, e.g.
    // `get_ambient(n).mem_facet_ref()` instead of
    // `n.facet_as<mem_facet>(get_ambient(n).mem_id())`. Every node must
    // have had `search_tree::set_ambient_context()` called on it with a
    // real `ambient_context_i` (not merely some other
    // `ambient_context_base`); if not, this throws `default_exception`
    // rather than silently degrading to an always-"unknown" fallback.
    ambient_ref<eq_tree::node, eq_tree::dep_tracker> get_ambient(eq_tree::node& n);
    ambient_ref<eq_tree::node const, eq_tree::dep_tracker> get_ambient(eq_tree::node const& n);

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

        // Trailed: for adding an equation (root construction or
        // mid-search alike - all constraint additions are trailed, no
        // exception). Undo just pops the pushed element.
        void add_equation(expr_ref_vector const& lhs, expr_ref_vector const& rhs, eq_tree::dep_tracker dep = nullptr) {
            m_eqs.push_back(equation(lhs, rhs, dep));
            m_trail.push(push_back_trail<equation>(m_eqs));
        }
        // Convenience overload: splits lhs/rhs into concat units and
        // delegates to the trailed vector form above.
        void add_equation(expr* lhs, expr* rhs, eq_tree::dep_tracker dep = nullptr) {
            expr_ref_vector lts(m), rts(m);
            u.str.get_concat_units(lhs, lts);
            u.str.get_concat_units(rhs, rts);
            add_equation(lts, rts, dep);
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
        std::ostream& display(std::ostream& out) const override;

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
        //
        // `n`/`id` identify this facet's own node/slot so that any forced
        // v:=epsilon substitution discovered during simplification can be
        // broadcast (via broadcast_subst) to every sibling subst_sink_i
        // facet (e.g. deq_facet) in the same node, not just applied to
        // this facet's own equations - NSB code review: simplify_equation
        // previously called apply_subst directly, silently skipping that
        // broadcast and leaving sibling facets holding a stale reference
        // to a variable this facet had already eliminated.
        bool simplify(eq_tree::node& n, ambient_context_i<eq_tree::dep_tracker>& ac, bool& conflict, eq_tree::dep_tracker& conflict_dep);
        ambient_context_i<eq_tree::dep_tracker>& ambient(eq_tree::node const& n) const;

    private:
        void apply_subst(expr* var, expr_ref_vector const& repl, eq_tree::dep_tracker subst_dep) override;
        // Simplify a single equation (by index into m_eqs) using
        // seq_rewriter::reduce_eq. Returns false and sets conflict=true
        // (and conflict_dep to the culprit equation's dependency) if the
        // equation is contradictory; otherwise returns true. Sets
        // changed=true if the equation's token lists were mutated or new
        // sub-equations were appended to m_eqs. On success, if both sides
        // reduced to empty, the equation is erased (trailed). `n`/`id` are
        // forwarded to broadcast_subst for any forced v:=epsilon
        // substitution (see simplify's comment above).
        bool simplify_equation(eq_tree::node& n, ambient_context_i<eq_tree::dep_tracker>& ac, unsigned idx, bool& conflict, eq_tree::dep_tracker& conflict_dep, bool& changed);
    };

    void broadcast_subst(eq_tree::node& target, expr* var, expr_ref_vector const& repl, eq_tree::dep_tracker subst_dep);

    // Deterministic propagation plugin wrapping eq_facet::simplify. Reads
    // its own facet id via the ambient context's eq_id() rather than a
    // constructor argument (see get_ambient()/ambient_context_i above).
    class eq_propagation : public eq_tree::propagation_plugin_i {
        ast_manager& m;
        seq_util&    u;
        struct stats {
            unsigned m_num_propagate = 0;
            unsigned m_num_progress  = 0;
            void reset() { *this = stats(); }
        };
        stats m_stats;
    public:
        eq_propagation(ast_manager& m, seq_util& u) : m(m), u(u) {}
        char const* name() const override { return "eq-propagate"; }
        stx::simplify_result propagate(eq_tree::node& n) override;
        void collect_statistics(::statistics& st) const override {
            st.update("eq-propagate num calls", m_stats.m_num_propagate);
            st.update("eq-propagate num progress", m_stats.m_num_progress);
        }
        void reset_statistics() override { m_stats.reset(); }
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
        struct stats {
            unsigned m_num_splits = 0;
            void reset() { *this = stats(); }
        };
        stats m_stats;

        class iterator : public eq_tree::split_iterator_i {
            eq_tree::node& m_n;
            ast_manager&   m;
            seq_util&      u;
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
            iterator(eq_tree::node& n, ast_manager& m, seq_util& u) : m_n(n), m(m), u(u) {}
            void push_back(char const* name, expr* var, expr_ref_vector const& repl, eq_tree::dep_tracker dep) {
                m_pending.push_back(alt{ name, var, repl, dep });
            }
            bool next(eq_tree::edge& out) override;
        };

    public:
        word_eq_split(ast_manager& m, seq_util& u) : m(m), u(u) {}
        char const* name() const override { return "nielsen-split"; }
        scoped_ptr<eq_tree::split_iterator_i> split(eq_tree::node& n, unsigned cost, eq_tree::edge& out, bool& has_more, bool& committed) override;
        void collect_statistics(::statistics& st) const override { st.update("nielsen-split num splits", m_stats.m_num_splits); }
        void reset_statistics() override { m_stats.reset(); }
    };

    // Refutation-only rule wrapping `seq_eq_approx::check` (see
    // seq_eq_approx.h's module comment), ported from the c3 branch's use
    // of exact word-length/segment-intersection refutation as an early,
    // cheap gate ahead of the Nielsen search proper. `seq_eq_approx`
    // itself has no notion of "branching": `check(lhs, rhs)` either
    // refutes the equation outright (l_false, an empty intersection of
    // the two sides' segment languages) or is inconclusive (l_true/
    // l_undef). There is therefore nothing to offer as a `split_plugin_i`
    // in the ordinary sense - this rule never actually branches - but the
    // user's design explicitly calls for implementing it as a *split*
    // plugin (not a propagation plugin) precisely so its priority
    // relative to every other split rule is controlled the same way
    // theirs is (registration order + `min_cost()`), rather than running
    // unconditionally to a fixpoint before any split is even considered
    // (which is what a propagation plugin would do, and which would give
    // it no way to defer to a cheaper split rule).
    //
    // `split()` iterates `eq_facet`'s current equations, feeding each to
    // a persistent `seq_eq_approx` instance (its derivative caches are
    // reused across calls; `reset_views()` is not needed since this rule
    // never calls `add_view`/`set_views` - each equation is checked with
    // no external view constraints, i.e. plain constant/variable
    // segments only). On the first refutation found (`l_false`), the
    // equation's own dependency justifies the conflict (segments over
    // plain tokens consult nothing beyond the equation's own sides, per
    // `seq_eq_approx`'s module comment: "An empty intersection refutes
    // the equation, because every value of a side lies in the language
    // of its segments" - no view/membership dependency is ever
    // introduced here since none is ever installed), `n.set_conflict`
    // is called directly and `split()` returns with `committed = false`
    // (no branch materialized - a pure refutation). If every equation is
    // inconclusive, the rule declines (`has_more = false`: nothing about
    // the equation set has changed since the last check, so retrying at
    // a higher cost cannot find a different answer without some other
    // rule first mutating `eq_facet`).
    //
    // Given a low `min_cost() == 0`, this is tried before every other
    // registered split plugin at cost 0 (see `theory_nseq.h`'s
    // registration-order table), mirroring the c3 branch's placement of
    // its own cheap pre-search refutation checks ahead of any
    // nondeterministic branching.
    class eq_approx_split : public eq_tree::split_plugin_i {
        ast_manager&    m;
        seq_util&       u;
        seq_rewriter&   m_rw;
        seq_eq_approx   m_approx;
        struct stats {
            unsigned m_num_checks = 0;
            unsigned m_num_refuted = 0;
            void reset() { *this = stats(); }
        };
        stats m_stats;
    public:
        eq_approx_split(ast_manager& m, seq_util& u, seq_rewriter& rw,
                        unsigned max_states = 1u << 12) :
            m(m), u(u), m_rw(rw), m_approx(rw, max_states) {
            set_min_cost(0);
        }
        char const* name() const override { return "eq-approx-split"; }
        scoped_ptr<eq_tree::split_iterator_i> split(eq_tree::node& n, unsigned cost, eq_tree::edge& out, bool& has_more, bool& committed) override;
        void collect_statistics(::statistics& st) const override {
            st.update("eq-approx-split num checks", m_stats.m_num_checks);
            st.update("eq-approx-split num refuted", m_stats.m_num_refuted);
        }
        void reset_statistics() override { m_stats.reset(); }
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
        struct stats {
            unsigned m_num_splits = 0;
            void reset() { *this = stats(); }
        };
        stats m_stats;

        // Classify a token's length as a known constant (chars, always 1
        // here since get_concat_units() explodes multi-char strings into
        // single-char tokens) or unknown/variable (anything else,
        // including fresh Skolem/opaque terms).
        static bool token_has_variable_length(seq_util& u, expr* tok) { return !u.str.is_unit(tok); }

    public:
        eq_split(ast_manager& m, seq_util& u) : m(m), u(u) {}
        char const* name() const override { return "eq-split"; }

        // Walk `lhs`/`rhs` token lists looking for a balanced interior
        // split point, as in the c3 branch's find_eq_split_point (see
        // module comment above and the .cpp implementation for the
        // per-token signed-balance algorithm and its history). Returns
        // false if no such point exists.
        static bool find_eq_split_point(seq_util& u, expr_ref_vector const& lhs, expr_ref_vector const& rhs,
                                         unsigned& out_lhs_idx, unsigned& out_rhs_idx, int& out_padding);

        scoped_ptr<eq_tree::split_iterator_i> split(eq_tree::node& n, unsigned cost, eq_tree::edge& out, bool& has_more, bool& committed) override;
        void collect_statistics(::statistics& st) const override { st.update("eq-split num splits", m_stats.m_num_splits); }
        void reset_statistics() override { m_stats.reset(); }
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

        // Trailed: for adding a disequation (root construction or
        // mid-search alike - all constraint additions are trailed, no
        // exception). Undo just pops the pushed element.
        void add_disequation(expr_ref_vector const& lhs, expr_ref_vector const& rhs, eq_tree::dep_tracker dep = nullptr) {
            m_diseqs.push_back(disequation(lhs, rhs, dep));
            m_trail.push(push_back_trail<disequation>(m_diseqs));
        }

        vector<disequation> const& disequations() const { return m_diseqs; }

        // Apply a substitution `var := repl` (chosen elsewhere, by
        // eq_facet's split plugin) to every pending disequation. Trailed
        // per-disequation (only entries containing `var` register undo).
        // The touched disequation's dependency is joined with
        // `subst_dep`, also trailed.
        void apply_subst(expr* var, expr_ref_vector const& repl, eq_tree::dep_tracker subst_dep) override;

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
        std::ostream& display(std::ostream& out) const override;

        // Deterministic simplification pass: prefix-stripping, then
        // discharge-on-symbol-clash / conflict-on-both-empty. On
        // conflict, sets `conflict_dep` to the culprit disequation's
        // dependency. See module comment. Trailed.
        bool simplify(bool& conflict, eq_tree::dep_tracker& conflict_dep);
    };

    // Deterministic propagation plugin wrapping deq_facet::simplify.
    // Reads its own facet id via the ambient context's deq_id().
    class deq_propagation : public eq_tree::propagation_plugin_i {
        ast_manager& m;
        seq_util&    u;
        struct stats {
            unsigned m_num_propagate = 0;
            void reset() { *this = stats(); }
        };
        stats m_stats;
    public:
        deq_propagation(ast_manager& m, seq_util& u) : m(m), u(u) {}
        char const* name() const override { return "deq-propagate"; }
        stx::simplify_result propagate(eq_tree::node& n) override;
        void collect_statistics(::statistics& st) const override { st.update("deq-propagate num calls", m_stats.m_num_propagate); }
        void reset_statistics() override { m_stats.reset(); }
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
        struct stats {
            unsigned m_num_splits = 0;
            void reset() { *this = stats(); }
        };
        stats m_stats;

        // Remaining alternatives (case 2, then case 3) after case 1 (if
        // offered) is the first, immediately materialized branch -
        // mirrors word_eq_split::iterator's "alt" list pattern.
        class iterator : public eq_tree::split_iterator_i {
            eq_tree::node& m_n;
            unsigned       m_diseq_idx;
            expr_ref_vector m_lhs, m_rhs; // the original disequation's sides, captured before any branch mutates the vector
            eq_tree::dep_tracker m_dep;
            unsigned       m_next_case; // 2, then 3, then done
            ast_manager&   m;
            seq_util&      u;
        public:
            iterator(eq_tree::node& n,
                      unsigned diseq_idx, expr_ref_vector const& lhs, expr_ref_vector const& rhs,
                      eq_tree::dep_tracker dep, unsigned next_case, ast_manager& m, seq_util& u) :
                m_n(n),
                m_diseq_idx(diseq_idx), m_lhs(lhs), m_rhs(rhs), m_dep(dep), m_next_case(next_case), m(m), u(u) {}
            bool next(eq_tree::edge& out) override;
        };

    public:
        deq_split(ast_manager& m, seq_util& u) : m(m), u(u) {}
        char const* name() const override { return "deq-split"; }
        scoped_ptr<eq_tree::split_iterator_i> split(eq_tree::node& n, unsigned cost, eq_tree::edge& out, bool& has_more, bool& committed) override;
        void collect_statistics(::statistics& st) const override { st.update("deq-split num splits", m_stats.m_num_splits); }
        void reset_statistics() override { m_stats.reset(); }
    };

} // namespace seq
