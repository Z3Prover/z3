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

Author:

    Nikolaj Bjorner (nbjorner) 2025-03-01

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

