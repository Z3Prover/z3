/*++
Copyright (c) 2025 Microsoft Corporation

Module Name:

    euf_sgraph.h

Abstract:

    Sequence/string graph layer

    Encapsulates string expressions in the style of euf_egraph.h.
    The sgraph registers sequence expressions and classifies them
    into a ZIPT-style representation of string tokens organized
    as binary concatenation trees.

    This provides a layer that maps Z3 AST expressions (from seq_decl_plugin)
    to snode structures with metadata for ground, regex-free, nullable, etc.

    ZIPT features not yet ported to snode/sgraph:
    
    -- Str operations (from StrManager):
       Normalisation: union-find style representative tracking (Normalised/IsNormalised)
       with cache migration (MoveCache) for equal strings with different tree structures.
       Balanced tree maintenance: DegenerationLevel tracking with rebalancing
       (Balanced/BalancedTrans properties on TupleStr).
       Concat simplification: merging adjacent Kleene stars (u.v* + v*w = u.v*w),
       merging adjacent loops (v{l1,h1} + v{l2,h2} = v{l1+l2,h1+h2}),
       absorbing nullable tokens next to .* (u.* + vw = u.*w when v nullable).
       Drop operations: DropLeft/DropRight for removing prefix/suffix tokens,
       with caching (DropLeftCache/DropRightCache on TupleStr).
       Substitution: Subst(var, replacement) and SubstChar operations with caching.
       Indexed access: GetIndex/GetIndexFwd/GetIndexBwd for token-level random access.
       Forward/reverse iteration: GetEnumerator/GetRevEnumerator over leaf tokens.
       ToList with caching: flattened token array with ListCache on TupleStr.
       Simplification: OptSimplify that unfolds constant powers and simplifies tokens.
       Derivative computation: Derivative(CharacterSet, fwd) for regex derivative construction.
       Equality: structural equality with associative hashing (TriangleMatrix-based rolling hash).
       Rotation equality: RotationEquals for detecting cyclic permutations.
       Expression reconstruction: ToExpr for converting back to Z3 AST.
       Graphviz export: ToDot for debugging visualisation.
    
    -- StrToken subclasses not yet mapped:
       SymCharToken: symbolic character variables (for regex unwinding).
       StrAtToken: str.at(s, i) as a named token with parent tracking.
       SubStrToken: str.substr(s, from, len) as a named token.
       SetToken: character set ranges (used for regex character classes).
       PostToken/PreToken: auxiliary regex position markers.
    
    -- StrToken features:
       GetDecomposition: Nielsen-style prefix/postfix decomposition with
       side constraints (IntConstraint) and variable substitutions (Subst).
       NamedStrToken parent/child extension tracking (Extension1/Extension2)
       for variable splitting (x = x'x'') with PowerExtension for x / u^n u'.
       CollectSymbols: gathering non-terminals and alphabet for Parikh analysis.
       MinTerms: FirstMinTerms/LastMinTerms for character class analysis.
       Token ordering: StrTokenOrder for deterministic comparison.
       Derivable flag: tracking which tokens support regex derivatives.
       BasicRegex flag: distinguishing basic vs extended regex constructs.

Author:

    Nikolaj Bjorner (nbjorner) 2025-03-01
    Clemens Eisenhofer 2025-03-01

--*/

#pragma once

#include "util/region.h"
#include "util/statistics.h"
#include "ast/ast.h"
#include "ast/seq_decl_plugin.h"
#include "ast/euf/euf_snode.h"

namespace euf {

    class sgraph {

        struct stats {
            unsigned m_num_nodes;
            unsigned m_num_concat;
            unsigned m_num_power;
            stats() { reset(); }
            void reset() { memset(this, 0, sizeof(*this)); }
        };

        ast_manager&     m;
        seq_util         m_seq;
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

        // register an expression and return its snode
        snode* mk(expr* e);

        // lookup an already-registered expression
        snode* find(expr* e) const;

        // build compound snodes
        snode* mk_empty(sort* s);
        snode* mk_concat(snode* a, snode* b);
        snode* mk_power(snode* base, snode* exp);

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

