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
       full_seq, to_re, in_re, other.
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
#include "ast/ast.h"
#include "ast/seq_decl_plugin.h"
#include "ast/rewriter/seq_rewriter.h"
#include "ast/euf/euf_snode.h"
#include "ast/euf/euf_egraph.h"

namespace euf {

    class seq_plugin;

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
        bool             m_add_plugin; // whether sgraph created the seq_plugin

        // maps expression id to snode
        ptr_vector<snode> m_expr2snode;

        // trail of alias entries (string constant → decomposed snode) for pop
        unsigned_vector  m_alias_trail;       // expression ids
        unsigned_vector  m_alias_trail_lim;   // scope boundaries

        snode* mk_snode(expr* e, snode_kind k, unsigned num_args, snode* const* args);
        snode_kind classify(expr* e) const;
        void compute_metadata(snode* n);
        void compute_hash_matrix(snode* n);
        void collect_re_predicates(snode* re, expr_ref_vector& preds);

    public:
        sgraph(ast_manager& m, egraph& eg, bool add_plugin = true);
        ~sgraph();

        ast_manager& get_manager() const { return m; }
        seq_util& get_seq_util() { return m_seq; }
        egraph& get_egraph() { return m_egraph; }
        egraph const& get_egraph() const { return m_egraph; }

        // register an expression and return its snode
        snode* mk(expr* e);

        // lookup an already-registered expression
        snode* find(expr* e) const;

        // register expression in both sgraph and egraph
        enode* mk_enode(expr* e);

        sort* get_str_sort() const { return m_str_sort; }

        // factory methods for creating snodes with corresponding expressions
        snode* mk_var(symbol const& name, sort* s);
        snode* mk_char(unsigned ch);
        snode *mk_empty_seq(sort *s);
        snode* mk_concat(snode* a, snode* b);

        // drop operations: remove tokens from the front/back of a concat tree
        snode* drop_first(snode* n);
        snode* drop_last(snode* n);
        snode* drop_left(snode* n, unsigned count);
        snode* drop_right(snode* n, unsigned count);

        // substitution: replace all occurrences of var in n by replacement
        snode* subst(snode* n, snode* var, snode* replacement);

        // Brzozowski derivative of regex re with respect to element elem.
        // allowed_range can explicitly provide a concrete character or range to use
        // for deriving symbolic variables.
        snode* brzozowski_deriv(snode* re, snode* elem, snode* allowed_range = nullptr);

        // compute minterms (character class partition) from a regex
        void compute_minterms(snode* re, snode_vector& minterms);

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

