/*++
Copyright (c) 2026 Microsoft Corporation

Module Name:

    euf_sgraph.h

Abstract:

    Sequence/string graph layer

    Encapsulates string and regex expressions for the string solver.
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

    Nikolaj Bjorner (nbjorner) 2026-03-01
    Clemens Eisenhofer 2026-03-01

--*/

#pragma once

#include "util/region.h"
#include "util/statistics.h"
#include "ast/ast.h"
#include "ast/seq_decl_plugin.h"
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
        egraph           m_egraph;
        region           m_region;
        snode_vector     m_nodes;
        expr_ref_vector  m_exprs;       // pin expressions
        unsigned_vector  m_scopes;
        unsigned         m_num_scopes = 0;
        stats            m_stats;

        // maps expression id to snode
        ptr_vector<snode> m_expr2snode;

        snode* mk_snode(expr* e, snode_kind k, unsigned num_args, snode* const* args);
        snode_kind classify(expr* e) const;
        void compute_metadata(snode* n);

    public:
        sgraph(ast_manager& m);
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

