/*++
Copyright (c) 2026 Microsoft Corporation

Module Name:

    seq_regex_bisim.h

Abstract:

    Union-find based bisimulation algorithm for symbolic regular expression
    equivalence, based on the construction described in:

      "Symbolic Extended Regular Expression Equivalence"
      Veanes, Bjorner et al., CAV'26 (see \git\ere\cav26\paper.tex)

    The algorithm decides equivalence of two regexes p, q by performing
    a bisimulation search on the symbolic derivative of p XOR q. A
    union-find structure tracks pairs of regex states that should be
    bisimilar, and the worklist is initialised with the singleton
    {p XOR q}.

    The algorithm returns:
        l_true   p and q are equivalent (bisimilar)
        l_false  p and q are inequivalent (a distinguishing prefix exists)
        l_undef  the algorithm could not decide within the configured bound
                 or encountered a non-ground regex it cannot reason about

Author:

    Nikolaj Bjorner (nbjorner)
    Margus Veanes   (veanes)

--*/
#pragma once

#include "ast/seq_decl_plugin.h"
#include "util/lbool.h"
#include "util/obj_hashtable.h"
#include "util/union_find.h"

class seq_rewriter;

namespace seq {

    /*
       Union-find based bisimulation algorithm for deciding equivalence
       of two ground (closed) regular expressions in ERE.

       Usage:

           seq::regex_bisim bisim(rewriter);
           lbool r = bisim.are_equivalent(p, q);
           if (r == l_true)  // p ≡ q
           if (r == l_false) // p ≢ q
           if (r == l_undef) // cannot decide

       The implementation only attempts the equivalence check on ground
       regexes (no free variables) that use the standard symbolic regex
       constructors. For non-ground or unsupported inputs the procedure
       conservatively returns l_undef.
    */
    class regex_bisim {
        ast_manager&             m;
        seq_rewriter&            m_rw;
        seq_util                 m_util;
        basic_union_find         m_uf;
        obj_map<expr, unsigned>  m_node_of;
        expr_ref_vector          m_pinned;
        expr_ref_vector          m_worklist;
        unsigned                 m_step_bound { 50000 };
        unsigned                 m_steps      { 0 };

        unsigned node_of(expr* r);
        bool merge_leaf(expr* xor_pair);
        bool collect_leaves(expr* der, expr_ref_vector& leaves);
        lbool nullability(expr* r);
        bool is_supported(expr* r);
        void reset();

    public:
        regex_bisim(seq_rewriter& rw);

        void set_step_bound(unsigned n) { m_step_bound = n; }

        lbool are_equivalent(expr* p, expr* q);
    };

}
