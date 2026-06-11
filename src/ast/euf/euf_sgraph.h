/*++
Copyright (c) 2026 Microsoft Corporation

Module Name:

    euf_sgraph.h

Abstract:

    Sequence/string graph layer

    Encapsulates string and regex expressions for the string solver.
    Implements the string graph layer from ZIPT (https://github.com/CEisenhofer/ZIPT/tree/parikh/ZIPT).
    The sgraph maps Z3 sequence/regex AST expressions to snode structures
    organized as binary concatenation trees with metadata, and owns an
    egraph with a seq_plugin for congruence closure.

    -- snode classification: empty, char, variable, unit, concat, power,
       star, loop, union, intersection, complement, fail, full_char,
       full_seq, range, to_re, in_re, other.
    -- Metadata computation: ground, regex_free, nullable, level, length.
    -- Expression registration via mk(expr*), lookup via find(expr*).
    -- Scope management: push/pop with backtracking.
    -- egraph ownership with seq_plugin for:
       * concat associativity via associativity-respecting hash table,
       * Kleene star merging (u.v*.v*.w = u.v*.w),
       * nullable absorption next to .* (u.*.v.w = u.*.w when v nullable),
       * str.++ identity elimination (concat(a, ε) = a),
       * re.++ identity/absorption (concat(a, epsilon) = a, concat(a, ∅) = ∅).
    -- enode registration via mk_enode(expr*).

    ZIPT features not yet ported:

    -- Str operations: normalisation with union-find representatives and
       cache migration, balanced tree maintenance, drop left/right with
       caching, substitution, indexed access, iteration, ToList caching,
       simplification, derivative computation, structural equality with
       associative hashing, rotation equality, expression reconstruction,
       Graphviz export.

    -- StrToken subclasses: SymCharToken, StrAtToken, SubStrToken,
       SetToken, PostToken/PreToken.

    -- StrToken features: Nielsen-style GetDecomposition with side
       constraints, NamedStrToken extension tracking for variable
       splitting with PowerExtension, CollectSymbols for Parikh analysis,
       MinTerms for character class analysis, token ordering, Derivable
       and BasicRegex flags.

Author:

    Clemens Eisenhofer 2026-03-01
    Nikolaj Bjorner (nbjorner) 2026-03-01

--*/

#pragma once

#include "util/region.h"
#include "util/statistics.h"
#include "util/lbool.h"
#include "ast/ast.h"
#include "ast/seq_decl_plugin.h"
#include "ast/rewriter/seq_rewriter.h"
#include "ast/euf/euf_snode.h"
#include "ast/euf/euf_egraph.h"

namespace euf {

    class seq_plugin;

    // Oracle queried by the projection-aware derivative of sgraph.
    // The projection operator π_{Q,F}(state) (a re.proj skolem) has its set of
    // explored states Q stored externally (the nielsen_graph partial DFA), keyed
    // by a snapshot index nu.  The sgraph consults this oracle to decide whether
    // the current state lies in Q when deriving a projection.
    class projection_oracle {
    public:
        virtual ~projection_oracle() = default;
        // true iff `state` (a regex expression) belongs to the explored
        // subautomaton snapshot identified by `nu`.
        virtual bool projection_state_in_Q(expr* state, unsigned nu) = 0;
    };

    class sgraph {

        struct stats {
            unsigned m_num_nodes;
            unsigned m_num_concat;
            unsigned m_num_power;
            unsigned m_num_hash_hits;
            stats() { reset(); }
            void reset() { memset(this, 0, sizeof(*this)); }
        };

        ast_manager&     m;
        seq_util         m_seq;
        seq_rewriter     m_rewriter;
        egraph&          m_egraph;
        region           m_region;
        snode_vector     m_nodes;
        sort_ref         m_str_sort;    // cached string sort
        unsigned_vector  m_scopes;
        unsigned         m_num_scopes = 0;
        stats            m_stats;

        // Pins every expression that any (live or popped) snode references via
        // m_expr.  snodes are allocated in m_region — which is never freed —
        // but their m_expr field is owned by the egraph trail.  Without this
        // pin the egraph would release expressions on pop while clients still
        // hold the matching snode* (e.g. inside nielsen_node str_mems, edge
        // substitutions, or the partial-DFA cache), turning every later
        // get_expr() into a use-after-free.  The pin grows monotonically; it
        // is dropped only when sgraph itself is destroyed.
        expr_ref_vector  m_pin;

        // maps expression id to snode
        ptr_vector<snode const> m_expr2snode;
        
        // trail of alias entries (string constant → decomposed snode) for pop
        unsigned_vector  m_alias_trail;       // expression ids
        unsigned_vector  m_alias_trail_lim;   // scope boundaries

        // Oracle answering "state ∈ Q_nu" for projection derivatives. Not owned.
        projection_oracle* m_proj_oracle = nullptr;

        snode* mk_snode(expr* e, snode_kind k, unsigned num_args, snode const** args);
        snode_kind classify(expr* e) const;
        void compute_metadata(snode* n);
        void compute_hash_matrix(snode* n);
        void collect_re_predicates(snode const* re, expr_ref_vector& preds);

    public:
        sgraph(ast_manager& m, egraph& eg, bool add_plugin = true);
        ~sgraph();

        ast_manager& get_manager() const { return m; }
        seq_util& get_seq_util() { return m_seq; }
        egraph& get_egraph() { return m_egraph; }
        egraph const& get_egraph() const { return m_egraph; }

        // register an expression and return its snode
        snode const* mk(expr* e);

        // lookup an already-registered expression
        snode const* find(expr* e) const;

        // register expression in both sgraph and egraph
        enode* mk_enode(expr* e);

        sort* get_str_sort() const { return m_str_sort; }

        // return true if a, b are of the same length and distinct
        bool are_unit_distinct(snode const* a, snode const* b) const;

        // factory methods for creating snodes with corresponding expressions
        snode const* mk_var(symbol const& name, sort* s);
        snode const* mk_char(unsigned ch);
        snode const *mk_empty_seq(sort *s);
        snode const* mk_concat(snode const* a, snode const* b);

        // drop operations: remove tokens from the front/back of a concat tree
        snode const* drop_first(snode const* n);
        snode const* drop_last(snode const* n);
        snode const* drop_left(snode const* n, unsigned count);
        snode const* drop_right(const snode* n, unsigned count);

        // substitution: replace all occurrences of var in n by replacement
        snode const* subst(snode const* n, snode const* var, snode const* replacement);

        // Brzozowski derivative of regex re with respect to element elem.
        // allowed_range can explicitly provide a concrete character or range to use
        // for deriving symbolic variables.
        snode const* brzozowski_deriv(snode const* re, snode const* elem);

        // Register the oracle consulted when deriving projection operators.
        // Passing nullptr unregisters. Not owned.
        void set_projection_oracle(projection_oracle* o) { m_proj_oracle = o; }

        // Projection operator support (π_{Q,F}(state) modeled as re.proj skolem).
        // Recognize and destructure a re.proj skolem expression.
        bool is_re_proj(expr* e, expr*& state, expr*& root, unsigned& nu) const;
        // Build the re.proj skolem expression for π_{{root}}(state) at snapshot nu.
        expr_ref mk_re_proj(expr* state, expr* root, unsigned nu);
        // True if e is a symbolic-character dispatch skeleton (ite / union of
        // dispatch, bottoming out in ∅) rather than a concrete regex state.
        bool is_char_dispatch(expr* e) const;
        // Wrap a (possibly ite/union-structured) symbolic-derivative result in
        // the projection operator, propagating π into every dispatch leaf (§4).
        expr_ref wrap_proj(expr* e, expr* root, unsigned nu);
        // Projection-aware Brzozowski derivative w.r.t. a character expr
        // (concrete or symbolic).
        snode const* deriv_proj(snode const* re, expr* ch);

        // Projection-aware nullability: lifts re.get_info().nullable to regexes
        // that may contain projection operators. Returns l_true / l_false
        // (l_undef only if an underlying projection-free subterm is undef).
        lbool re_nullable(snode const* re);

        // Decode a character expression that may be represented as a const-char,
        // a unit string containing a const-char, or a one-character string literal.
        bool decode_re_char(expr* ex, unsigned& out) const;

        // compute minterms (character class partition) from a regex
        void compute_minterms(snode const* re, snode_vector& minterms);

        // scope management for backtracking
        void push();
        void pop(unsigned num_scopes);

        // access
        snode_vector const& nodes() const { return m_nodes; }
        unsigned num_nodes() const { return m_nodes.size(); }

        // display
        std::ostream& display(std::ostream& out) const;

        void collect_statistics(statistics& st) const;
    };

}

