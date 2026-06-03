/*++
Copyright (c) 2025 Microsoft Corporation

Module Name:

    seq_derive.h

Abstract:

    Symbolic derivative computation for regular expressions.
    Produces an ITE-tree (transition regex) representation where
    the free variable is de Bruijn index 0 representing the input character.

    Based on the theory of symbolic derivatives and transition regexes:
    - Veanes et al., "On Symbolic Derivatives and Transition Regexes" (LPAR 2024)
    - Varatalu, Veanes, Ernits, "RE#" (POPL 2025)
    - Stanford, Veanes, Bjørner, "Symbolic Boolean Derivatives" (PLDI 2021)

Authors:

    Nikolaj Bjorner (nbjorner) 2025-06-03

--*/

#pragma once

#include "ast/seq_decl_plugin.h"
#include "ast/arith_decl_plugin.h"
#include "ast/array_decl_plugin.h"
#include "ast/rewriter/bool_rewriter.h"

namespace seq {

    /**
     * Symbolic derivative engine for regular expressions.
     *
     * Given a regex r, operator()(r) computes a symbolic derivative δ(r)
     * represented as an ITE-tree over character predicates (using de Bruijn
     * variable 0 for the character). Evaluating the ITE-tree for a concrete
     * character 'a' yields the classical Brzozowski derivative δ_a(r).
     *
     * The ITE-tree structure implicitly defines minterms (equivalence classes
     * of characters indistinguishable by the regex).
     *
     * Key properties:
     * - Results are memoized for termination on cyclic derivative graphs
     * - Union/intersection operands are sorted for ACI canonicalization
     * - Depth-bounded to prevent stack overflow
     */
    class derive {
        ast_manager&    m;
        seq_util        m_util;
        arith_util      m_autil;
        bool_rewriter   m_br;

        // Cache: maps regex expr to its symbolic derivative
        obj_map<expr, expr*> m_cache;
        expr_ref_vector      m_trail;    // pin cached results

        // Depth limiting
        unsigned m_depth { 0 };
        static const unsigned m_max_depth = 512;

        seq_util::rex& re() { return m_util.re; }
        seq_util& u() { return m_util; }

        // The element (character) for the current derivative computation
        expr_ref m_ele;

        // Core derivative computation
        expr_ref derive_rec(expr* r);
        expr_ref derive_core(expr* r);

        // Helpers for specific regex constructs
        expr_ref derive_to_re(expr* s, sort* seq_sort);
        expr_ref derive_range(expr* lo, expr* hi, sort* seq_sort);
        expr_ref derive_of_pred(expr* pred, sort* seq_sort);

        // Nullable check: returns a Boolean expression
        expr_ref is_nullable(expr* r);

        // Smart constructors with simplification and ACI canonicalization
        expr_ref mk_union(expr* a, expr* b);
        expr_ref mk_inter(expr* a, expr* b);
        expr_ref mk_concat(expr* a, expr* b);
        expr_ref mk_complement(expr* a);
        expr_ref mk_ite(expr* c, expr* t, expr* e);

        // Flatten and sort for ACI normal form
        void flatten_union(expr* r, expr_ref_vector& args);
        void flatten_inter(expr* r, expr_ref_vector& args);
        expr_ref mk_union_from_sorted(expr_ref_vector& args);
        expr_ref mk_inter_from_sorted(expr_ref_vector& args);

        // ITE-tree binary combinator (analogous to REsharp mk_binary)
        // Combines two ITE-tree derivatives with a binary regex operation
        expr_ref ite_combine_binary(expr* d1, expr* d2,
            std::function<expr_ref(expr*, expr*)> const& op);

        // ITE-tree unary combinator (analogous to REsharp mk_unary)
        expr_ref ite_combine_unary(expr* d, std::function<expr_ref(expr*)> const& op);

        // Distribute concatenation through ITE/union in derivative
        expr_ref mk_deriv_concat(expr* d, expr* tail);

        sort* re_sort(expr* r) { return r->get_sort(); }
        sort* seq_sort(expr* r) { sort* s = nullptr; m_util.is_re(r, s); return s; }
        sort* ele_sort(expr* r) { sort* s = seq_sort(r); sort* e = nullptr; m_util.is_seq(s, e); return e; }

    public:
        derive(ast_manager& m);

        /**
         * Compute the derivative of regex r with respect to element ele.
         * When ele is a de Bruijn variable, produces a symbolic ITE-tree.
         * When ele is a concrete character, produces the concrete derivative.
         */
        expr_ref operator()(expr* ele, expr* r);

        /**
         * Convenience: symbolic derivative using de Bruijn var 0.
         */
        expr_ref operator()(expr* r);

        void reset();
    };

}

