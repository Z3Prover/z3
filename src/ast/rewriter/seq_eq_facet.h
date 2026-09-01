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
#include "util/stx_search_tree.h"

namespace seq {

    // Dependency source leaf type for this standalone (theory_nseq-free)
    // instantiation of the search tree: word-equation solving needs no
    // external SAT/EUF justification, so a plain unsigned tag (unused here,
    // but required by stx::search_tree's template parameter) suffices.
    using eq_tree = stx::search_tree<unsigned>;

    // A flattened side of a word equation: a sequence of tokens, each
    // either a length-1 string constant or an opaque variable/term.
    // Reference-counted (rather than a raw ptr_vector<expr>) since tokens
    // may be freshly-created variables (e.g. from mk_fresh_var) that
    // nothing else in the system is holding a reference to.
    using token_list = expr_ref_vector;

    // Flatten a str-sort expr (a str.++ chain, possibly a bare leaf) into
    // its token list: constants are exploded into one token per character;
    // any other leaf (variable or otherwise-opaque term) becomes a single
    // token. `u` must be the seq_util of `e`'s ast_manager.
    void flatten(seq_util& u, expr* e, token_list& out);

    // Is `e` a length-1 string constant?
    bool is_const_token(seq_util& u, expr* e);

    // Replace every occurrence of `var` in `ts` with the tokens of `repl`
    // (order-preserving splice). Shared helper between `eq_facet` and
    // `deq_facet` (and any future facet holding token-list equations).
    void subst_in(token_list& ts, expr* var, token_list const& repl);

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
        virtual void apply_subst(expr* var, token_list const& repl) = 0;
    };

    /**
     * Facet holding a set of pending word equations. Equations are
     * discharged (removed) as soon as they are solved; the facet is
     * satisfied when the set is empty.
     */
    class eq_facet : public stx::facet_i, public subst_sink_i {
    public:
        struct equation {
            token_list m_lhs;
            token_list m_rhs;
            equation(token_list const& lhs, token_list const& rhs) : m_lhs(lhs), m_rhs(rhs) {}
            bool operator<(equation const& other) const;
            bool operator==(equation const& other) const;
        };

    private:
        ast_manager& m;
        seq_util&    u;
        vector<equation> m_eqs;

    public:
        eq_facet(ast_manager& m, seq_util& u) : m(m), u(u) {}

        ast_manager& get_manager() const { return m; }
        seq_util& get_seq_util() const { return u; }

        void add_equation(token_list const& lhs, token_list const& rhs) {
            m_eqs.push_back(equation(lhs, rhs));
        }
        void add_equation(expr* lhs, expr* rhs) {
            token_list lts(m), rts(m);
            flatten(u, lhs, lts);
            flatten(u, rhs, rts);
            add_equation(lts, rts);
        }

        vector<equation> const& equations() const { return m_eqs; }

        // Apply a forced/branch substitution `var := repl` to every
        // equation currently in the facet.
        void apply_subst(expr* var, token_list const& repl) override;

        // Allocate a fresh opaque variable token of `s`'s sort.
        expr* mk_fresh_var(sort* s) { return m.mk_fresh_const("t", s); }

        // -- stx::facet_i --
        facet_i* clone() const override;
        unsigned hash() const override;
        bool similar(facet_i const& other) const override;
        bool is_satisfied() const override { return m_eqs.empty(); }

        // Deterministic simplification pass: prefix-stripping, forced
        // empty-side substitution, trivial-equation removal, symbol-clash
        // detection. See module comment. Returns true if the equation set
        // changed (informational only - the engine detects the fixed
        // point itself via facet hashing).
        bool simplify(bool& conflict);
    };

    // Deterministic propagation plugin wrapping eq_facet::simplify.
    class eq_propagation : public eq_tree::propagation_plugin_i {
        stx::facet_id m_id;
    public:
        explicit eq_propagation(stx::facet_id id) : m_id(id) {}
        char const* name() const override { return "eq-propagate"; }
        stx::simplify_result propagate(eq_tree::node& n) override;
    };

    // Nielsen-transformation split plugin: branches the first equation
    // whose leading tokens are not both resolved by propagation (i.e. a
    // variable paired with a constant, or two distinct variables).
    class word_eq_split : public eq_tree::split_plugin_i {
        eq_tree&      m_tree;
        stx::facet_id m_id;
    public:
        word_eq_split(eq_tree& tree, stx::facet_id id) : m_tree(tree), m_id(id) {}
        char const* name() const override { return "nielsen-split"; }
        bool split(eq_tree::node& n, unsigned cost, ptr_vector<eq_tree::edge>& out) override;
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
            token_list m_lhs;
            token_list m_rhs;
            disequation(token_list const& lhs, token_list const& rhs) : m_lhs(lhs), m_rhs(rhs) {}
            bool operator<(disequation const& other) const;
            bool operator==(disequation const& other) const;
        };

    private:
        ast_manager& m;
        seq_util&    u;
        vector<disequation> m_diseqs;

    public:
        deq_facet(ast_manager& m, seq_util& u) : m(m), u(u) {}

        ast_manager& get_manager() const { return m; }
        seq_util& get_seq_util() const { return u; }

        void add_disequation(token_list const& lhs, token_list const& rhs) {
            m_diseqs.push_back(disequation(lhs, rhs));
        }
        void add_disequation(expr* lhs, expr* rhs) {
            token_list lts(m), rts(m);
            flatten(u, lhs, lts);
            flatten(u, rhs, rts);
            add_disequation(lts, rts);
        }

        vector<disequation> const& disequations() const { return m_diseqs; }

        // Apply a substitution `var := repl` (chosen elsewhere, by
        // eq_facet's split plugin) to every pending disequation.
        void apply_subst(expr* var, token_list const& repl) override;

        // -- stx::facet_i --
        facet_i* clone() const override;
        unsigned hash() const override;
        bool similar(facet_i const& other) const override;
        bool is_satisfied() const override { return m_diseqs.empty(); }

        // Deterministic simplification pass: prefix-stripping, then
        // discharge-on-symbol-clash / conflict-on-both-empty. See module
        // comment.
        bool simplify(bool& conflict);
    };

    // Deterministic propagation plugin wrapping deq_facet::simplify.
    class deq_propagation : public eq_tree::propagation_plugin_i {
        stx::facet_id m_id;
    public:
        explicit deq_propagation(stx::facet_id id) : m_id(id) {}
        char const* name() const override { return "deq-propagate"; }
        stx::simplify_result propagate(eq_tree::node& n) override;
    };

} // namespace seq
