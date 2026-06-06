/*++
Copyright (c) 2026 Microsoft Corporation

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
#include "util/obj_pair_hashtable.h"

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

        // Cache: maps (ele, regex) pair to its derivative
        obj_pair_map<expr, expr, expr*> m_cache;
        obj_pair_map<expr, expr, expr*> m_top_cache; // post-simplify cache
        expr_ref_vector      m_trail;    // pin cached results

        // Op cache for ITE-hoisting operations (union, inter, concat, complement)
        obj_pair_map<expr, expr, expr*> m_union_cache;
        obj_pair_map<expr, expr, expr*> m_inter_cache;
        obj_pair_map<expr, expr, expr*> m_concat_cache;
        obj_map<expr, expr*>            m_complement_cache;

        // Depth limiting
        unsigned m_depth { 0 };
        static const unsigned m_max_depth = 512;

        // Simplify ITE recursion depth limit
        unsigned m_simp_depth { 0 };
        static const unsigned m_max_simp_depth = 8;

        // ITE combine depth limit (bounds exponential blowup in BDD merge)
        unsigned m_inter_hoist_depth { 0 };
        static const unsigned m_max_inter_hoist_depth = 4;

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
        expr_ref mk_union_core(expr* a, expr* b);
        expr_ref mk_inter(expr* a, expr* b);
        expr_ref mk_inter_core(expr* a, expr* b);
        expr_ref mk_concat(expr* a, expr* b);
        expr_ref mk_complement(expr* a);
        expr_ref mk_complement_core(expr* a);
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
        expr_ref mk_deriv_concat_core(expr* d, expr* tail);

        // Extract head character and tail from a sequence expression
        bool get_head_tail(expr* s1, expr* s2, expr_ref& hd, expr_ref& tl);

        // Lightweight subsumption check: returns true if L(a) ⊆ L(b)
        bool is_subset(expr* a, expr* b);

        // Predicate implication for character range conditions.
        // Returns true if condition a implies condition b.
        bool pred_implies(expr* a, expr* b);
        bool extract_char_range(expr* cond, unsigned& lo, unsigned& hi);

        // Normalize reverse(r) by pushing reverse inward
        expr_ref normalize_reverse(expr* r);

        // Path of signed conditions for ITE simplification
        using path_t = svector<std::pair<expr*, bool>>;
        using intervals_t = svector<std::pair<unsigned, unsigned>>;

        // Simplify ITE conditions w.r.t. m_ele and path knowledge
        expr_ref simplify_ite(expr* d);
        expr_ref simplify_ite_rec(path_t& path, intervals_t& intervals, expr* d, unsigned depth);
        std::pair<expr_ref, expr_ref> simplify_ite_rec(path_t& path, intervals_t& intervals, expr* c, expr* t, expr* e, unsigned depth);
        lbool push_path(path_t& path, expr* c, bool sign);
        lbool push_intervals(intervals_t& intervals, expr* c, bool sign);
        lbool eval_cond(expr* cond);
        lbool eval_range_cond(intervals_t const& intervals, expr* c);
        static void intersect_intervals(unsigned lo, unsigned hi, intervals_t& ranges);
        static void exclude_interval(unsigned lo, unsigned hi, intervals_t& ranges, unsigned max_char);

        sort* re_sort(expr* r) { return r->get_sort(); }
        sort* seq_sort(expr* r) { sort* s = nullptr; m_util.is_re(r, s); return s; }
        sort* ele_sort(expr* r) { sort* s = seq_sort(r); sort* e = nullptr; m_util.is_seq(s, e); return e; }

        void reset();

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

        /**
         * Lightweight structural subsumption check: L(a) ⊆ L(b)?
         * Returns true only when provable structurally.
         */
        bool subsumes(expr* larger, expr* smaller) { return is_subset(smaller, larger); }
    };

}

