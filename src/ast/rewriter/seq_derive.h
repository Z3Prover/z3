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
#include "util/obj_triple_hashtable.h"
#include <functional>

class seq_rewriter;

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
        seq_rewriter&   m_re;

        // Cache: maps (ele, regex) pair to its derivative
        obj_pair_map<expr, expr, expr*> m_cache;
        obj_pair_map<expr, expr, expr*> m_top_cache; // post-simplify cache
        expr_ref_vector      m_trail;    // pin cached results

        // Op cache for ITE-hoisting operations (union, inter, concat, complement)
        // Path-aware caches: key is (a, b, path_expr) for binary ops, (a, path_expr) for complement
        obj_triple_map<expr, expr, expr, expr *> m_union_cache, m_inter_cache, m_xor_cache;
        obj_pair_map<expr, expr, expr*> m_concat_cache;
        obj_pair_map<expr, expr, expr*> m_complement_cache;

        // Depth limiting
        unsigned m_depth { 0 };
        static const unsigned m_max_depth = 512;

        seq_util::rex& re() { return m_util.re; }
        seq_util& u() { return m_util; }

        bool m_antimirov_derivative = true;

        // The element (character) for the current derivative computation
        expr_ref m_ele;

        // Path state for inline pruning during mk_inter/mk_union/mk_complement
        using intervals_t = svector<std::pair<unsigned, unsigned>>;

        // Path: vector of signed atoms
        svector<std::pair<expr*, bool>> m_path;
        // Intervals: feasible character ranges under current path (append-only)
        intervals_t m_intervals;
        unsigned m_intervals_start { 0 };
        // Stack of saved states for push/pop
        struct path_save { unsigned path_sz; unsigned intervals_sz; unsigned intervals_start; expr* path_expr; };
        svector<path_save> m_path_stack;
        // Boolean expression encoding of current path (for cache keys)
        expr_ref m_path_expr;

        // Path interface
        lbool push(expr* c, bool sign);  // l_true: implied, l_undef: pushed (must pop), l_false: contradicts
        void  pop();                      // restore state to matching push
        expr* get_path_expr() { return m_path_expr; }

        // Hoist ITE: apply_op through ite(c, t, e) with path pruning
        expr_ref apply_ite(expr* c, expr* t, expr* e, expr* r, std::function<expr_ref(expr*, expr*)> apply_op);
        expr_ref apply_ite(expr* c, expr* t1, expr* e1, expr* t2, expr* e2, std::function<expr_ref(expr*, expr*)> apply_op);
        expr_ref apply_ite(expr* c, expr* t, expr* e, std::function<expr_ref(expr*)> apply_op);
        // Common ITE dispatch for binary ops (union/inter)
        expr_ref hoist_ite(expr* a, expr* b, std::function<expr_ref(expr*, expr*)> apply_op);

        // Evaluate a condition against the current path/intervals
        lbool eval_path_cond(expr* c);

        // Internal helpers for push
        lbool push_path_atoms(expr* c, bool sign);
        lbool push_intervals_impl(expr* c, bool sign);

        // Core derivative computation
        expr_ref derive_rec(expr* r);
        expr_ref derive_core(expr* r);

        // Helpers for specific regex constructs
        expr_ref derive_to_re(expr* s, sort* seq_sort);
        expr_ref derive_range(expr* lo, expr* hi, sort* seq_sort);
        expr_ref derive_of_pred(expr* pred, sort* seq_sort);

        // Nullable check: returns a Boolean expression
        expr_ref is_nullable(expr* r);
        expr_ref is_nullable_symbolic_regex(expr* r, sort* seq_sort);

        // Smart constructors with path-aware simplification and ACI canonicalization
        expr_ref mk_union(expr* a, expr* b);
        bool are_complements(expr* a, expr* b);
        unsigned union_id(expr* e);              // complement-aware ID for sorting
        bool is_subset(expr* a, expr* b);
        expr_ref mk_union_core(expr* a, expr* b); 
        expr_ref mk_inter(expr* a, expr* b);
        expr_ref mk_inter_core(expr* a, expr* b); 
        expr_ref mk_concat(expr* a, expr* b);
        expr_ref mk_complement(expr* a);
        expr_ref mk_complement_core(expr* a);
        expr_ref mk_xor(expr *a, expr *b);
        expr_ref mk_xor_core(expr *a, expr *b);
        expr_ref mk_core(decl_kind k, expr* a, expr* b);
        expr_ref mk_ite(expr* c, expr* t, expr* e);

        // Distribute concatenation through ITE/union in derivative
        expr_ref mk_deriv_concat(expr* d, expr* tail);
        expr_ref mk_deriv_concat_core(expr* d, expr* tail);

        // Extract head character and tail from a sequence expression
        bool get_head_tail(expr* s1, expr* s2, expr_ref& hd, expr_ref& tl);

        // Predicate implication for character range conditions.
        bool pred_implies(bool sign_a, expr* a, bool sign_b, expr* b);
        bool pred_implies(expr* a, expr* b);

        // Normalize reverse(r)
        expr_ref mk_regex_reverse(expr* r);

        // Condition evaluation helpers
        lbool eval_cond(expr* cond);
        lbool eval_range_cond(expr* c);
        void intersect_intervals(unsigned lo, unsigned hi);
        void exclude_interval(unsigned lo, unsigned hi);

        sort* re_sort(expr* r) { return r->get_sort(); }
        sort* seq_sort(expr* r) { sort* s = nullptr; m_util.is_re(r, s); return s; }
        sort* ele_sort(expr* r) { sort* s = seq_sort(r); sort* e = nullptr; m_util.is_seq(s, e); return e; }

        void reset();
        void reset_op_caches();

    public:
        derive(ast_manager& m, seq_rewriter& re);

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
         * Nullable check: returns a Boolean expression that is true iff r accepts the empty string.
         */
        expr_ref nullable(expr* r) { return is_nullable(r); }


        void set_antimirov(bool flag) {
            m_antimirov_derivative = flag;
        }
    };

}
