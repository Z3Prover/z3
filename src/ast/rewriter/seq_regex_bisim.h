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

class statistics;
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
    public:
        // Aggregate counters across all regex_bisim invocations on this
        // thread. Exposed via collect_statistics so `-st` reports them.
        struct stats_t {
            unsigned           m_queries     = 0;   // total are_equivalent calls
            unsigned           m_decided     = 0;   // returned l_true or l_false
            unsigned           m_undef       = 0;   // returned l_undef
            // Per-reason undef counters (sum = m_undef):
            unsigned           m_undef_unsupported = 0; // is_supported(p) || is_supported(q) failed
            unsigned           m_undef_nullable    = 0; // a nullability check returned l_undef
            unsigned           m_undef_leaf        = 0; // collect_leaves saw an unknown node
            unsigned           m_undef_steps       = 0; // step bound exceeded
            unsigned           m_steps_total = 0;   // worklist steps consumed
            unsigned long long m_time_us_total = 0; // wall time in micros
        };

        static stats_t const& get_stats();
        static void reset_stats();
        static void collect_statistics(::statistics& st);

    private:
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

        lbool are_equivalent_core(expr* p, expr* q);

    public:
        regex_bisim(seq_rewriter& rw);

        void set_step_bound(unsigned n) { m_step_bound = n; }

        lbool are_equivalent(expr* p, expr* q);
    };

}
