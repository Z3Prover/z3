/*++
Copyright (c) 2026 Microsoft Corporation

Module Name:

    seq_derive.cpp

Abstract:

    Symbolic derivative computation for regular expressions.
    Produces an ITE-tree (transition regex) representation following
    the approach of RE# (Varatalu, Veanes, Ernits - POPL 2025).

    The symbolic derivative δ(r) maps each character to the resulting
    derivative state via an ITE-tree. The free variable (:var 0) represents
    the input character.

Authors:

    Nikolaj Bjorner (nbjorner) 2026-06-03

--*/

#include "ast/rewriter/seq_derive.h"
#include "ast/rewriter/seq_rewriter.h"
#include "ast/ast_pp.h"
#include "ast/array_decl_plugin.h"
#include "ast/rewriter/bool_rewriter.h"
#include "util/util.h"
#include <algorithm>

namespace seq {

    derive::derive(ast_manager& m, seq_rewriter& re) :
        m(m),
        m_util(m),
        m_autil(m),
        m_br(m),
        m_re(re),
        m_trail(m),
        m_ele(m),
        m_path_expr(m) {
        m_br.set_flat_and_or(false);
    }

    void derive::reset() {
        m_cache.reset();
        m_top_cache.reset();
        m_union_cache.reset();
        m_inter_cache.reset();
        m_concat_cache.reset();
        m_complement_cache.reset();
        m_trail.reset();
    }

    // Reset only operation caches (union/inter/concat/complement)
    // while preserving derivative caches (m_cache, m_top_cache)
    void derive::reset_op_caches() {
        m_union_cache.reset();
        m_inter_cache.reset();
        m_concat_cache.reset();
        m_complement_cache.reset();
    }

    expr_ref derive::operator()(expr* ele, expr* r) {
        SASSERT(m_util.is_re(r));
        if (m_trail.size() > 500000)
            reset();
        else if (m_trail.size() > 100000)
            reset_op_caches();
        // Check top-level cache (post-simplify result)
        expr* cached = nullptr;
        if (m_top_cache.find(ele, r, cached))
            return expr_ref(cached, m);
        m_ele = ele;
        m_depth = 0;
        // Initialize path state for inline pruning
        m_path.reset();
        m_intervals.reset();
        m_intervals.push_back(std::make_pair(0u, u().max_char()));
        m_path_expr = m.mk_true();
        expr_ref result = derive_rec(r);
        m_ele = nullptr;
        // Cache and pin the final result
        m_top_cache.insert(ele, r, result);
        m_trail.push_back(ele);
        m_trail.push_back(r);
        m_trail.push_back(result);
        return result;
    }

    expr_ref derive::operator()(expr* r) {
        SASSERT(m_util.is_re(r));
        sort* seq_sort = nullptr, * ele_sort = nullptr;
        VERIFY(m_util.is_re(r, seq_sort));
        VERIFY(m_util.is_seq(seq_sort, ele_sort));
        expr_ref v(m.mk_var(0, ele_sort), m);
        return (*this)(v, r);
    }

    // -------------------------------------------------------
    // Core derivative computation
    // -------------------------------------------------------

    expr_ref derive::derive_rec(expr* r) {
        SASSERT(m_util.is_re(r));

        // Check cache (indexed by both m_ele and r)
        expr* cached = nullptr;
        if (m_cache.find(m_ele, r, cached))
            return expr_ref(cached, m);

        // Depth check
        if (m_depth >= m_max_depth) {
            // Return stuck derivative (the derivative operator applied symbolically)
            return expr_ref(re().mk_derivative(m_ele, r), m);
        }

        flet<unsigned> _scoped_depth(m_depth, m_depth + 1);
        expr_ref result = derive_core(r);

        // Cache the result
        m_cache.insert(m_ele, r, result);
        m_trail.push_back(m_ele);
        m_trail.push_back(r);
        m_trail.push_back(result);
        return result;
    }

    // Forward declaration helper
    expr_ref derive::derive_core(expr* r) {
        sort* s = nullptr;
        VERIFY(m_util.is_re(r, s));

        auto nothing = [&]() { return expr_ref(re().mk_empty(r->get_sort()), m); };
        auto epsilon = [&]() { return expr_ref(re().mk_to_re(u().str.mk_empty(s)), m); };
        auto dotstar = [&]() { return expr_ref(re().mk_full_seq(r->get_sort()), m); };

        expr* r1 = nullptr;
        expr* r2 = nullptr;
        expr* cond = nullptr;
        unsigned lo = 0, hi = 0;

        // δ(∅) = ∅, δ(ε) = ∅
        if (re().is_empty(r) || re().is_epsilon(r))
            return nothing();

        // δ(Σ*) = Σ*, δ(.+) = Σ*
        if (re().is_full_seq(r) || re().is_dot_plus(r))
            return dotstar();

        // δ(.) = ε (full char accepts any single character)
        if (re().is_full_char(r))
            return epsilon();

        // δ(str.to_re(s)) - derivative of a literal string
        if (re().is_to_re(r, r1))
            return derive_to_re(r1, s);

        // δ(re.range(lo, hi)) - character range
        if (re().is_range(r, r1, r2))
            return derive_range(r1, r2, s);

        // δ(re.of_pred(p)) - predicate-based regex
        if (re().is_of_pred(r, r1))
            return derive_of_pred(r1, s);

        // δ(r1 · r2) = δ(r1) · r2 ∪ (if nullable(r1) then δ(r2) else ∅)
        if (re().is_concat(r, r1, r2)) {
            expr_ref d1 = derive_rec(r1);
            expr_ref d1_r2 = mk_deriv_concat(d1, r2);
            expr_ref nullable_r1 = is_nullable(r1);
            if (m.is_true(nullable_r1))
                return mk_union(d1_r2, derive_rec(r2));
            if (m.is_false(nullable_r1))
                return d1_r2;
            // Conditional: nullable is a Boolean expression
            expr_ref d2 = derive_rec(r2);
            expr_ref guarded = mk_ite(nullable_r1, d2, nothing());
            return mk_union(d1_r2, guarded);
        }

        // δ(r1 ∪ r2) = δ(r1) ∪ δ(r2)
        if (re().is_union(r, r1, r2)) {
            expr_ref d1 = derive_rec(r1);
            expr_ref d2 = derive_rec(r2);
            return mk_union(d1, d2);
        }

        // δ(r1 ∩ r2) = δ(r1) ∩ δ(r2)
        if (re().is_intersection(r, r1, r2)) {
            expr_ref d1 = derive_rec(r1);
            expr_ref d2 = derive_rec(r2);
            return mk_inter(d1, d2);
        }

        // δ(~r1) = ~δ(r1)
        if (re().is_complement(r, r1)) {
            expr_ref d1 = derive_rec(r1);
            return mk_complement(d1);
        }

        // δ(r1*) = δ(r1) · r1*
        if (re().is_star(r, r1)) {
            expr_ref d1 = derive_rec(r1);
            expr_ref star_r1(re().mk_star(r1), m);
            return mk_deriv_concat(d1, star_r1);
        }

        // δ(r1+) = δ(r1) · r1*
        if (re().is_plus(r, r1)) {
            expr_ref d1 = derive_rec(r1);
            expr_ref star_r1(re().mk_star(r1), m);
            return mk_deriv_concat(d1, star_r1);
        }

        // δ(r1?) = δ(r1)
        if (re().is_opt(r, r1))
            return derive_rec(r1);

        // δ(r1{lo,hi})
        if (re().is_loop(r, r1, lo, hi)) {
            if (hi == 0 || hi < lo)
                return nothing();
            expr_ref d1 = derive_rec(r1);
            expr_ref tail(re().mk_loop_proper(r1, (lo == 0 ? 0 : lo - 1), hi - 1), m);
            return mk_deriv_concat(d1, tail);
        }

        // δ(r1{lo,}) - unbounded loop
        if (re().is_loop(r, r1, lo)) {
            expr_ref d1 = derive_rec(r1);
            expr_ref tail(re().mk_loop(r1, (lo == 0 ? 0 : lo - 1)), m);
            return mk_deriv_concat(d1, tail);
        }

        // δ(r1 \ r2) = δ(r1) ∩ ~δ(r2)
        if (re().is_diff(r, r1, r2)) {
            expr_ref d1 = derive_rec(r1);
            expr_ref d2 = derive_rec(r2);
            expr_ref neg_d2 = mk_complement(d2);
            return mk_inter(d1, neg_d2);
        }

        // δ(ite(c, r1, r2)) = ite(c, δ(r1), δ(r2))
        if (m.is_ite(r, cond, r1, r2)) {
            expr_ref d1 = derive_rec(r1);
            expr_ref d2 = derive_rec(r2);
            return mk_ite(cond, d1, d2);
        }

        // δ(reverse(r1)) - normalize by pushing reverse inward, then derive
        if (re().is_reverse(r, r1)) {
            expr_ref norm = normalize_reverse(r1);
            if (norm != r)
                return derive_rec(norm);
            return expr_ref(re().mk_derivative(m_ele, r), m);
        }

        // Stuck/uninterpreted case
        return expr_ref(re().mk_derivative(m_ele, r), m);
    }

    // -------------------------------------------------------
    // Derivative of specific regex constructs
    // -------------------------------------------------------

    expr_ref derive::derive_to_re(expr* s, sort* seq_sort) {
        sort* re_sort = re().mk_re(seq_sort);
        // δ(to_re("")) = ∅
        if (u().str.is_empty(s))
            return expr_ref(re().mk_empty(re_sort), m);

        // δ(to_re("c₁c₂...cₙ")) = ite(ele = c₁, to_re("c₂...cₙ"), ∅)
        zstring zs;
        if (u().str.is_string(s, zs)) {
            if (zs.length() == 0)
                return expr_ref(re().mk_empty(re_sort), m);
            // First character
            expr_ref head(m_util.mk_char(zs[0]), m);
            expr_ref cond(m.mk_eq(m_ele, head), m);
            // Tail string
            expr_ref tail_str(u().str.mk_string(zs.extract(1, zs.length() - 1)), m);
            expr_ref tail_re(re().mk_to_re(tail_str), m);
            expr_ref empty(re().mk_empty(re_sort), m);
            return mk_ite(cond, tail_re, empty);
        }

        // δ(to_re(unit(c))) = ite(ele = c, ε, ∅)
        expr* ch = nullptr;
        if (u().str.is_unit(s, ch)) {
            expr_ref eps(re().mk_to_re(u().str.mk_empty(seq_sort)), m);
            expr_ref empty(re().mk_empty(re_sort), m);
            expr_ref cond(m.mk_eq(m_ele, ch), m);
            return mk_ite(cond, eps, empty);
        }

        // δ(to_re(s1 ++ s2)) = ite(head matches, to_re(tail ++ s2), ∅)
        expr* s1 = nullptr, * s2 = nullptr;
        if (u().str.is_concat(s, s1, s2)) {
            expr_ref hd(m), tl(m);
            if (get_head_tail(s1, s2, hd, tl)) {
                expr_ref cond(m.mk_eq(m_ele, hd), m);
                expr_ref tail_re(re().mk_to_re(tl), m);
                expr_ref empty(re().mk_empty(re_sort), m);
                return mk_ite(cond, tail_re, empty);
            }
        }

        // δ(to_re(itos(n))) - derivative of integer-to-string
        // itos(n) produces digits '0'-'9' when n >= 0, empty when n < 0
        expr* n = nullptr;
        if (u().str.is_itos(s, n)) {
            expr_ref empty(re().mk_empty(re_sort), m);
            // Guard: n >= 0 and element is a digit and element = s[0]
            expr_ref n_ge_0(m_autil.mk_ge(n, m_autil.mk_int(0)), m);
            expr_ref char_0(m_util.mk_char('0'), m);
            expr_ref char_9(m_util.mk_char('9'), m);
            expr_ref ge_0(m_util.mk_le(char_0, m_ele), m);
            expr_ref le_9(m_util.mk_le(m_ele, char_9), m);
            expr_ref is_digit(m.mk_and(ge_0, le_9), m);
            // First character of itos(n) matches ele
            expr_ref zero_idx(m_autil.mk_int(0), m);
            expr_ref first(u().str.mk_nth_i(s, zero_idx), m);
            expr_ref eq_first(m.mk_eq(m_ele, first), m);
            // Guard = n >= 0 && is_digit && ele = s[0]
            expr_ref guard(m.mk_and(n_ge_0, m.mk_and(is_digit, eq_first)), m);
            // Tail: to_re(substr(itos(n), 1, len(itos(n)) - 1))
            expr_ref one(m_autil.mk_int(1), m);
            expr_ref len(u().str.mk_length(s), m);
            expr_ref rest_len(m_autil.mk_sub(len, one), m);
            expr_ref rest(u().str.mk_substr(s, one, rest_len), m);
            expr_ref rest_re(re().mk_to_re(rest), m);
            return mk_ite(guard, rest_re, empty);
        }

        // Non-ground sequence: δ(to_re(s)) = ite(s ≠ "" ∧ ele = s[0], to_re(s[1:]), ∅)
        expr_ref empty_seq(u().str.mk_empty(seq_sort), m);
        expr_ref is_non_empty(m.mk_not(m.mk_eq(s, empty_seq)), m);
        expr_ref zero(m_autil.mk_int(0), m);
        expr_ref first(u().str.mk_nth_i(s, zero), m);
        expr_ref eq_first(m.mk_eq(m_ele, first), m);
        expr_ref guard(m.mk_and(is_non_empty, eq_first), m);
        expr_ref one(m_autil.mk_int(1), m);
        expr_ref len(u().str.mk_length(s), m);
        expr_ref rest_len(m_autil.mk_sub(len, one), m);
        expr_ref rest(u().str.mk_substr(s, one, rest_len), m);
        expr_ref rest_re(re().mk_to_re(rest), m);
        expr_ref empty(re().mk_empty(re_sort), m);
        return mk_ite(guard, rest_re, empty);
    }

    expr_ref derive::derive_range(expr* lo, expr* hi, sort* seq_sort) {
        sort* re_sort = re().mk_re(seq_sort);
        expr_ref empty(re().mk_empty(re_sort), m);
        expr_ref eps(re().mk_to_re(u().str.mk_empty(seq_sort)), m);

        // Extract character values from unit strings
        expr_ref c_lo(m), c_hi(m);
        if (u().str.is_unit_string(lo, c_lo) && u().str.is_unit_string(hi, c_hi)) {
            // Build range condition, simplifying trivial bounds
            unsigned lo_val = 0, hi_val = 0;
            bool lo_trivial = m_util.is_const_char(c_lo, lo_val) && lo_val == 0;
            bool hi_trivial = m_util.is_const_char(c_hi, hi_val) && hi_val == u().max_char();

            if (lo_trivial && hi_trivial)
                return eps; // full charset range — always matches

            expr_ref in_range(m);
            if (lo_trivial)
                in_range = m_util.mk_le(m_ele, c_hi);
            else if (hi_trivial)
                in_range = m_util.mk_le(c_lo, m_ele);
            else
                in_range = m.mk_and(m_util.mk_le(c_lo, m_ele), m_util.mk_le(m_ele, c_hi));

            return mk_ite(in_range, eps, empty);
        }

        // Fallback: stuck derivative
        return expr_ref(re().mk_derivative(m_ele, re().mk_range(lo, hi)), m);
    }

    expr_ref derive::derive_of_pred(expr* pred, sort* seq_sort) {
        sort* re_sort = re().mk_re(seq_sort);
        expr_ref empty(re().mk_empty(re_sort), m);
        expr_ref eps(re().mk_to_re(u().str.mk_empty(seq_sort)), m);

        // Apply predicate to the element
        array_util autil(m);
        expr* args[2] = { pred, m_ele };
        expr_ref cond(autil.mk_select(2, args), m);
        return mk_ite(cond, eps, empty);
    }

    // Extract head character and remaining tail from a sequence
    // s1 is the first part, s2 is the continuation (from str.concat(s1, s2))
    bool derive::get_head_tail(expr* s1, expr* s2, expr_ref& hd, expr_ref& tl) {
        expr* ch = nullptr;
        expr* a = nullptr, * b = nullptr;
        if (u().str.is_unit(s1, ch)) {
            hd = ch;
            tl = s2;
            return true;
        }
        if (u().str.is_concat(s1, a, b)) {
            expr_ref new_s2(u().str.mk_concat(b, s2), m);
            return get_head_tail(a, new_s2, hd, tl);
        }
        zstring zs;
        if (u().str.is_string(s1, zs) && zs.length() > 0) {
            hd = m_util.mk_char(zs[0]);
            if (zs.length() == 1)
                tl = s2;
            else {
                expr_ref rest(u().str.mk_string(zs.extract(1, zs.length() - 1)), m);
                tl = u().str.mk_concat(rest, s2);
            }
            return true;
        }
        return false;
    }

    // -------------------------------------------------------
    // Normalize reverse by pushing it inward
    // -------------------------------------------------------

    expr_ref derive::normalize_reverse(expr* r) {
        expr* r1 = nullptr, * r2 = nullptr, * s = nullptr, * p = nullptr;
        unsigned lo = 0, hi = 0;
        zstring zs;

        // reverse(reverse(r1)) = r1
        if (re().is_reverse(r, r1))
            return expr_ref(r1, m);

        // reverse(r1 · r2) = reverse(r2) · reverse(r1)
        if (re().is_concat(r, r1, r2)) {
            expr_ref a(re().mk_reverse(r2), m);
            expr_ref b(re().mk_reverse(r1), m);
            return expr_ref(re().mk_concat(a, b), m);
        }

        // reverse(r1 ∪ r2) = reverse(r1) ∪ reverse(r2)
        if (re().is_union(r, r1, r2)) {
            expr_ref a(re().mk_reverse(r1), m);
            expr_ref b(re().mk_reverse(r2), m);
            return expr_ref(re().mk_union(a, b), m);
        }

        // reverse(r1 ∩ r2) = reverse(r1) ∩ reverse(r2)
        if (re().is_intersection(r, r1, r2)) {
            expr_ref a(re().mk_reverse(r1), m);
            expr_ref b(re().mk_reverse(r2), m);
            return expr_ref(re().mk_inter(a, b), m);
        }

        // reverse(r1 \ r2) = reverse(r1) \ reverse(r2)
        if (re().is_diff(r, r1, r2)) {
            expr_ref a(re().mk_reverse(r1), m);
            expr_ref b(re().mk_reverse(r2), m);
            return expr_ref(re().mk_diff(a, b), m);
        }

        // reverse(ite(c, r1, r2)) = ite(c, reverse(r1), reverse(r2))
        if (m.is_ite(r, p, r1, r2))
            return expr_ref(m.mk_ite(p, re().mk_reverse(r1), re().mk_reverse(r2)), m);

        // reverse(r1?) = reverse(r1)?
        if (re().is_opt(r, r1))
            return expr_ref(re().mk_opt(re().mk_reverse(r1)), m);

        // reverse(~r1) = ~reverse(r1)
        if (re().is_complement(r, r1))
            return expr_ref(re().mk_complement(re().mk_reverse(r1)), m);

        // reverse(r1*) = reverse(r1)*
        if (re().is_star(r, r1))
            return expr_ref(re().mk_star(re().mk_reverse(r1)), m);

        // reverse(r1+) = reverse(r1)+
        if (re().is_plus(r, r1))
            return expr_ref(re().mk_plus(re().mk_reverse(r1)), m);

        // reverse(r1{lo,}) = reverse(r1){lo,}
        if (re().is_loop(r, r1, lo))
            return expr_ref(re().mk_loop(re().mk_reverse(r1), lo), m);

        // reverse(r1{lo,hi}) = reverse(r1){lo,hi}
        if (re().is_loop(r, r1, lo, hi))
            return expr_ref(re().mk_loop_proper(re().mk_reverse(r1), lo, hi), m);

        // Symmetric: full_seq, empty, range, full_char, of_pred
        if (re().is_full_seq(r) || re().is_empty(r) || re().is_range(r) ||
            re().is_full_char(r) || re().is_of_pred(r))
            return expr_ref(r, m);

        // reverse(to_re(s)) where s is a string literal
        if (re().is_to_re(r, s) && u().str.is_string(s, zs))
            return expr_ref(re().mk_to_re(u().str.mk_string(zs.reverse())), m);

        // reverse(to_re(unit)) = to_re(unit)
        if (re().is_to_re(r, s) && u().str.is_unit(s))
            return expr_ref(r, m);

        // reverse(to_re(s1 ++ s2)) = reverse(to_re(s2)) · reverse(to_re(s1))
        if (re().is_to_re(r, s) && u().str.is_concat(s, r1, r2)) {
            expr_ref a(re().mk_reverse(re().mk_to_re(r2)), m);
            expr_ref b(re().mk_reverse(re().mk_to_re(r1)), m);
            return expr_ref(re().mk_concat(a, b), m);
        }

        // Stuck — cannot normalize further
        return expr_ref(re().mk_reverse(r), m);
    }

    // -------------------------------------------------------
    // Nullability - uses info class from seq_decl_plugin.h
    // -------------------------------------------------------

    expr_ref derive::is_nullable(expr* r) {
        // First, try the static info which handles ground/interpreted regex
        lbool nb = re().get_info(r).nullable;
        if (nb == l_true)
            return expr_ref(m.mk_true(), m);
        if (nb == l_false)
            return expr_ref(m.mk_false(), m);
        // For symbolic regexes, return a membership predicate
        sort* s = nullptr;
        VERIFY(m_util.is_re(r, s));
        return expr_ref(re().mk_in_re(u().str.mk_empty(s), r), m);
    }

    // -------------------------------------------------------
    // Smart constructors with simplification
    // -------------------------------------------------------


    // Extract character range [lo, hi] from a derivative condition.
    // Conditions are of the form:
    //   ele == c                                          → range [c, c]
    //   char_le(lo_expr, ele) && char_le(ele, hi_expr)  → range [lo, hi]
    //   char_le(lo_expr, ele)                           → range [lo, max_char]
    //   char_le(ele, hi_expr)                           → range [0, hi]
    // Returns false if not a recognizable range condition.
    bool derive::extract_char_range(expr* cond, unsigned& lo, unsigned& hi) {
        expr* e1 = nullptr, *e2 = nullptr, *lhs = nullptr, *rhs = nullptr;
        lo = 0;
        hi = u().max_char();

        // Negation: not handled here — handled via pred_implies logic
        if (m.is_not(cond, e1))
            return false;

        // Equality: ele == c → range [c, c]
        if (m.is_eq(cond, e1, e2)) {
            unsigned v;
            if (u().is_const_char(e1, v) && e2 == m_ele) {
                lo = hi = v;
                return true;
            }
            if (u().is_const_char(e2, v) && e1 == m_ele) {
                lo = hi = v;
                return true;
            }
            return false;
        }

        // Conjunction: and(char_le(lo, x), char_le(x, hi))
        if (m.is_and(cond, e1, e2)) {
            expr *a1, *a2, *b1, *b2;
            unsigned v;
            if (u().is_char_le(e1, a1, a2)) {
                if (u().is_const_char(a1, v) && a2 == m_ele)
                    lo = std::max(lo, v); // v <= ele
                else if (a1 == m_ele && u().is_const_char(a2, v))
                    hi = std::min(hi, v); // ele <= v
            }
            if (u().is_char_le(e2, b1, b2)) {
                unsigned v2;
                if (u().is_const_char(b1, v2) && b2 == m_ele)
                    lo = std::max(lo, v2); // v2 <= ele
                else if (b1 == m_ele && u().is_const_char(b2, v2))
                    hi = std::min(hi, v2); // ele <= v2
            }
            return lo <= hi;
        }

        // Single char_le
        if (u().is_char_le(cond, lhs, rhs)) {
            unsigned v;
            if (u().is_const_char(lhs, v) && rhs == m_ele) {
                lo = v; // v <= ele
                return true;
            }
            if (lhs == m_ele && u().is_const_char(rhs, v)) {
                hi = v; // ele <= v
                return true;
            }
        }

        return false;
    }

    // Predicate implication for character range conditions.
    // Returns true if: whenever cond_a is true, cond_b must also be true.
    // Used for BDD-merge of derivative ITE trees.
    // pred_implies(sign_a, a, sign_b, b): does (sign_a ? ¬a : a) imply (sign_b ? ¬b : b)?
    bool derive::pred_implies(bool sign_a, expr* a, bool sign_b, expr* b) {
        // Same atom: check sign compatibility
        if (a == b) return sign_a == sign_b;

        // Both negated: ¬a → ¬b iff b → a, i.e. pred_implies(false, b, false, a)
        if (sign_a && sign_b)
            return pred_implies(false, b, false, a);

        unsigned lo_a, hi_a, lo_b, hi_b;

        if (!sign_a && !sign_b) {
            // a → b: range_a ⊆ range_b
            if (extract_char_range(a, lo_a, hi_a) && extract_char_range(b, lo_b, hi_b))
                return lo_b <= lo_a && hi_a <= hi_b;
        }
        else if (!sign_a && sign_b) {
            // a → ¬b: range_a ∩ range_b = ∅
            if (extract_char_range(a, lo_a, hi_a) && extract_char_range(b, lo_b, hi_b))
                return hi_a < lo_b || hi_b < lo_a;
        }
        else if (sign_a && !sign_b) {
            // ¬a → b: complement of range_a ⊆ range_b
            if (extract_char_range(a, lo_a, hi_a) && extract_char_range(b, lo_b, hi_b))
                return lo_b == 0 && hi_b >= u().max_char();
        }

        return false;
    }

    bool derive::pred_implies(expr* a, expr* b) {
        expr* nota = nullptr, * notb = nullptr;
        bool sign_a = m.is_not(a, nota);
        bool sign_b = m.is_not(b, notb);
        return pred_implies(sign_a, sign_a ? nota : a, sign_b, sign_b ? notb : b);
    }

    expr_ref derive::mk_union(expr* a, expr* b) {
        // Check path-aware op cache
        expr* pe = get_path_expr();
        expr* cached = nullptr;
        if (m_union_cache.find(a, b, pe, cached))
            return expr_ref(cached, m);

        expr_ref result = mk_union_core(a, b);

        // Store in cache
        m_union_cache.insert(a, b, pe, result);
        m_trail.push_back(a);
        m_trail.push_back(b);
        m_trail.push_back(pe);
        m_trail.push_back(result);
        return result;
    }

    // Lightweight structural subsumption: checks if L(a) ⊆ L(b)
    bool derive::is_subset(expr* a, expr* b) {
        if (a == b) return true;
        if (re().is_empty(a)) return true;
        if (re().is_full_seq(b)) return true;

        expr* b1 = nullptr;
        if (re().is_plus(b, b1) && re().is_full_char(b1) &&
            re().get_info(a).nullable == l_false)
            return true;

        if (re().is_star(b, b1) && a == b1) return true;

        expr* a1 = nullptr;
        if (re().is_star(a, a1) && re().is_star(b, b1) && is_subset(a1, b1)) return true;

        if (re().is_union(b, b1, a1)) {
            if (is_subset(a, b1) || is_subset(a, a1)) return true;
        }
        if (re().is_union(a, a1, b1)) {
            if (is_subset(a1, b) && is_subset(b1, b)) return true;
        }
        if (re().is_intersection(a, a1, b1)) {
            if (is_subset(a1, b) || is_subset(b1, b)) return true;
        }
        if (re().is_intersection(b, b1, a1)) {
            if (is_subset(a, b1) && is_subset(a, a1)) return true;
        }

        expr* a2 = nullptr, * b2 = nullptr;
        if (re().is_concat(a, a1, a2) && re().is_concat(b, b1, b2) &&
            is_subset(a1, b1) && is_subset(a2, b2))
            return true;

        // loop subsumption: r{la,ua} ⊆ r{lb,ub} when lb <= la and ua <= ub
        unsigned la, ua, lb, ub;
        if (re().is_loop(a, a1, la, ua) && re().is_loop(b, b1, lb, ub) &&
            a1 == b1 && lb <= la && ua <= ub)
            return true;

        if (re().is_complement(a, a1) && re().is_complement(b, b1))
            return is_subset(b1, a1);

        return false;
    }

    void derive::flatten_union(expr* e, expr_ref_vector& args) {
        expr* a, *b;
        if (re().is_union(e, a, b)) {
            flatten_union(a, args);
            flatten_union(b, args);
        } else {
            args.push_back(e);
        }
    }

    expr_ref derive::mk_union_core(expr* a, expr* b) {
        // Canonical order: smaller id first
        if (a->get_id() > b->get_id())
            std::swap(a, b);

        // Identity / annihilator
        if (a == b) return expr_ref(a, m);
        if (re().is_empty(a)) return expr_ref(b, m);
        if (re().is_empty(b)) return expr_ref(a, m);
        if (re().is_full_seq(a)) return expr_ref(a, m);
        if (re().is_full_seq(b)) return expr_ref(b, m);

        // Complement absorption: r ∪ ~r = Σ*
        expr* c = nullptr;
        if (re().is_complement(a, c) && c == b)
            return expr_ref(re().mk_full_seq(a->get_sort()), m);
        if (re().is_complement(b, c) && c == a)
            return expr_ref(re().mk_full_seq(a->get_sort()), m);

        // ITE handling with path pruning
        expr *c1, *t1, *e1, *c2, *t2, *e2;
        auto union_op = [&](expr* x, expr* y) { return mk_union(x, y); };

        if (m.is_ite(a, c1, t1, e1) && m.is_ite(b, c2, t2, e2)) {
            expr_ref r(m);
            if (c1 == c2)
                r = apply_ite(c1, t1, e1, t2, e2, union_op);
            else
                r = apply_ite(c1, t1, e1, b, union_op);
            if (r) return r;
            return expr_ref(re().mk_empty(a->get_sort()), m);
        }
        if (m_path_stack.size() < 8) {
            if (m.is_ite(a, c1, t1, e1)) {
                expr_ref r = apply_ite(c1, t1, e1, b, union_op);
                if (r) return r;
                return expr_ref(re().mk_empty(a->get_sort()), m);
            }
            if (m.is_ite(b, c2, t2, e2)) {
                expr_ref r = apply_ite(c2, t2, e2, a, union_op);
                if (r) return r;
                return expr_ref(re().mk_empty(a->get_sort()), m);
            }
        }

        // Prefix factoring: a·x ∪ a·y = a·(x ∪ y)
        expr *a1, *a2, *b1, *b2;
        if (re().is_concat(a, a1, a2) && re().is_concat(b, b1, b2) && a1 == b1) {
            expr_ref tail = mk_union(a2, b2);
            return mk_deriv_concat(a1, tail);
        }

        // star absorbs epsilon: r* ∪ ε = r*
        if (re().is_star(a) && re().is_epsilon(b)) return expr_ref(a, m);
        if (re().is_star(b) && re().is_epsilon(a)) return expr_ref(b, m);

        // Subsumption: a ∪ b = b if a ⊆ b, a ∪ b = a if b ⊆ a
        if (is_subset(a, b)) return expr_ref(b, m);
        if (is_subset(b, a)) return expr_ref(a, m);

        // ACI normalization: flatten, sort by id, deduplicate
        expr_ref_vector args(m);
        flatten_union(a, args);
        flatten_union(b, args);
        std::sort(args.data(), args.data() + args.size(), [](expr* x, expr* y) { return x->get_id() < y->get_id(); });
        expr_ref result(args.get(0), m);
        for (unsigned i = 1; i < args.size(); ++i) {
            if (args.get(i) != args.get(i - 1))
                result = expr_ref(re().mk_union(result, args.get(i)), m);
        }
        return result;
    }

    expr_ref derive::mk_inter(expr* a, expr* b) {
        // Check path-aware op cache
        expr* pe = get_path_expr();
        expr* cached = nullptr;
        if (m_inter_cache.find(a, b, pe, cached))
            return expr_ref(cached, m);

        expr_ref result = mk_inter_core(a, b);

        // Store in cache
        m_inter_cache.insert(a, b, pe, result);
        m_trail.push_back(a);
        m_trail.push_back(b);
        m_trail.push_back(pe);
        m_trail.push_back(result);
        return result;
    }

    expr_ref derive::mk_inter_core(expr* a, expr* b) {
        // Canonical order: smaller id first
        if (a->get_id() > b->get_id())
            std::swap(a, b);

        // Identity / annihilator
        if (a == b) return expr_ref(a, m);
        if (re().is_empty(a)) return expr_ref(a, m);
        if (re().is_empty(b)) return expr_ref(b, m);
        if (re().is_full_seq(a)) return expr_ref(b, m);
        if (re().is_full_seq(b)) return expr_ref(a, m);

        // Complement absorption: r ∩ ~r = ∅
        expr* c = nullptr;
        if (re().is_complement(a, c) && c == b)
            return expr_ref(re().mk_empty(a->get_sort()), m);
        if (re().is_complement(b, c) && c == a)
            return expr_ref(re().mk_empty(a->get_sort()), m);

        // ITE handling with path pruning
        expr *c1, *t1, *e1, *c2, *t2, *e2;
        auto inter_op = [&](expr* x, expr* y) { return mk_inter(x, y); };

        if (m.is_ite(a, c1, t1, e1) && m.is_ite(b, c2, t2, e2)) {
            expr_ref r(m);
            if (c1 == c2)
                r = apply_ite(c1, t1, e1, t2, e2, inter_op);
            else
                r = apply_ite(c1, t1, e1, b, inter_op);
            if (r) return r;
            return expr_ref(re().mk_empty(a->get_sort()), m);
        }
        if (m_path_stack.size() < 8) {
            if (m.is_ite(a, c1, t1, e1)) {
                expr_ref r = apply_ite(c1, t1, e1, b, inter_op);
                if (r) return r;
                return expr_ref(re().mk_empty(a->get_sort()), m);
            }
            if (m.is_ite(b, c2, t2, e2)) {
                expr_ref r = apply_ite(c2, t2, e2, a, inter_op);
                if (r) return r;
                return expr_ref(re().mk_empty(a->get_sort()), m);
            }
        }

        // Base case: build raw intersection
        return expr_ref(re().mk_inter(a, b), m);
    }

    expr_ref derive::mk_concat(expr* a, expr* b) {
        if (re().is_empty(a)) return expr_ref(a, m);
        if (re().is_empty(b)) return expr_ref(b, m);
        if (re().is_epsilon(a)) return expr_ref(b, m);
        if (re().is_epsilon(b)) return expr_ref(a, m);

        // to_re(s1) · to_re(s2) → to_re(s1 ++ s2)
        expr* s1 = nullptr, * s2 = nullptr;
        if (re().is_to_re(a, s1) && re().is_to_re(b, s2))
            return expr_ref(re().mk_to_re(u().str.mk_concat(s1, s2)), m);

        // r* · r* → r*
        expr* a1 = nullptr, * b1 = nullptr;
        if (re().is_star(a, a1) && re().is_star(b, b1) && a1 == b1)
            return expr_ref(a, m);

        // Right-associate: (a · b) · c → a · (b · c)
        if (re().is_concat(a, a1, b1)) {
            expr_ref tail = mk_concat(b1, b);
            return expr_ref(re().mk_concat(a1, tail), m);
        }

        return expr_ref(re().mk_concat(a, b), m);
    }

    expr_ref derive::mk_complement(expr* a) {
        // Check path-aware op cache
        expr* pe = get_path_expr();
        expr* cached = nullptr;
        if (m_complement_cache.find(a, pe, cached))
            return expr_ref(cached, m);

        expr_ref result = mk_complement_core(a);

        // Store in cache
        m_complement_cache.insert(a, pe, result);
        m_trail.push_back(a);
        m_trail.push_back(pe);
        m_trail.push_back(result);
        return result;
    }

    expr_ref derive::mk_complement_core(expr* a) {
        // ~~r → r
        expr* r = nullptr;
        if (re().is_complement(a, r))
            return expr_ref(r, m);
        // ~∅ → Σ*
        if (re().is_empty(a))
            return expr_ref(re().mk_full_seq(a->get_sort()), m);
        // ~Σ* → ∅
        if (re().is_full_seq(a))
            return expr_ref(re().mk_empty(a->get_sort()), m);

        // Push through ITE with path pruning: ~(ite(c, t, e)) → ite(c, ~t, ~e)
        expr* c, * t, * e;
        if (m.is_ite(a, c, t, e)) {
            auto comp_op = [&](expr* x) { return mk_complement(x); };
            expr_ref r = apply_ite(c, t, e, comp_op);
            if (r) return r;
            return expr_ref(re().mk_full_seq(a->get_sort()), m);
        }

        // ~ε → .+
        sort* s = nullptr;
        expr* r1 = nullptr;
        if (re().is_to_re(a, r1) && u().str.is_empty(r1)) {
            VERIFY(m_util.is_re(a, s));
            return expr_ref(re().mk_plus(re().mk_full_char(a->get_sort())), m);
        }

        return expr_ref(re().mk_complement(a), m);
    }

    expr_ref derive::mk_ite(expr* c, expr* t, expr* e) {
        if (m.is_true(c) || t == e)
            return expr_ref(t, m);
        if (m.is_false(c))
            return expr_ref(e, m);
        // Use path-aware condition evaluation
        lbool cond_val = eval_path_cond(c);
        if (cond_val == l_true) return expr_ref(t, m);
        if (cond_val == l_false) return expr_ref(e, m);
        return expr_ref(m.mk_ite(c, t, e), m);
    }

    // -------------------------------------------------------
    // Distribute concat through ITE/union structure of derivative
    // -------------------------------------------------------

    expr_ref derive::mk_deriv_concat(expr* d, expr* tail) {
        // Check op cache
        expr* cached = nullptr;
        if (m_concat_cache.find(d, tail, cached))
            return expr_ref(cached, m);

        expr_ref result = mk_deriv_concat_core(d, tail);

        // Store in cache
        m_concat_cache.insert(d, tail, result);
        m_trail.push_back(d);
        m_trail.push_back(tail);
        m_trail.push_back(result);
        return result;
    }

    expr_ref derive::mk_deriv_concat_core(expr* d, expr* tail) {
        expr_ref _d(d, m), _tail(tail, m);
        expr* c, * t, * e;

        if (re().is_empty(d))
            return expr_ref(d, m);
        if (re().is_epsilon(d))
            return expr_ref(tail, m);

        if (m.is_ite(d, c, t, e)) {
            expr_ref then_r = mk_deriv_concat(t, tail);
            expr_ref else_r = mk_deriv_concat(e, tail);
            return mk_ite(c, then_r, else_r);
        }

        if (re().is_union(d, t, e)) {
            expr_ref left = mk_deriv_concat(t, tail);
            expr_ref right = mk_deriv_concat(e, tail);
            return mk_union(left, right);
        }

        return mk_concat(d, tail);
    }

    // -------------------------------------------------------
    // Path management for inline pruning
    // -------------------------------------------------------

    lbool derive::push(expr* c, bool sign) {
        // Check if (c, sign) is already determined by the path
        lbool cv = eval_path_cond(c);
        if (cv == l_true && !sign) return l_true;   // c implied true, push(c,false) is redundant
        if (cv == l_false && sign) return l_true;   // c implied false, push(c,true) is redundant  
        if (cv == l_true && sign) return l_false;   // c implied true, push(c,true) contradicts
        if (cv == l_false && !sign) return l_false; // c implied false, push(c,false) contradicts

        // Save current state
        unsigned saved_path_sz = m_path.size();
        intervals_t saved_intervals(m_intervals);
        expr* saved_path_expr = m_path_expr;

        // Push atoms onto path and check for contradiction or implication
        lbool atoms_result = push_path_atoms(c, sign);
        if (atoms_result == l_false) {
            m_path.shrink(saved_path_sz);
            m_intervals = saved_intervals;
            return l_false;
        }

        // Update intervals
        lbool intervals_result = push_intervals_impl(c, sign);
        if (intervals_result == l_false) {
            m_path.shrink(saved_path_sz);
            m_intervals = saved_intervals;
            return l_false;
        }

        // If both determined the atom is implied, no need to actually push
        if (atoms_result == l_true && intervals_result == l_true) {
            m_path.shrink(saved_path_sz);
            m_intervals = saved_intervals;
            return l_true;
        }

        // Update path expression
        expr* atom = sign ? m.mk_not(c) : c;
        m_path_expr = m.mk_and(m_path_expr, atom);
        m_trail.push_back(m_path_expr);

        // Commit: save state for pop()
        m_path_stack.push_back({ saved_path_sz, std::move(saved_intervals), saved_path_expr });
        return l_undef;
    }

    void derive::pop() {
        SASSERT(!m_path_stack.empty());
        auto const& saved = m_path_stack.back();
        m_path.shrink(saved.path_sz);
        m_intervals = saved.intervals;
        m_path_expr = saved.path_expr;
        m_path_stack.pop_back();
    }

    // Binary apply_ite: hoist ite(c, t, e) op r with path pruning
    expr_ref derive::apply_ite(expr* c, expr* t, expr* e, expr* r, std::function<expr_ref(expr*, expr*)> apply_op) {
        expr_ref then_br(m), else_br(m);
        switch (push(c, false)) {
        case l_true:  return apply_op(t, r);
        case l_undef: then_br = apply_op(t, r); pop(); break;
        case l_false: break;
        }
        switch (push(c, true)) {
        case l_true:  return apply_op(e, r);
        case l_undef: else_br = apply_op(e, r); pop(); break;
        case l_false: break;
        }
        if (then_br && else_br) return mk_ite(c, then_br, else_br);
        if (then_br) return then_br;
        if (else_br) return else_br;
        return expr_ref(nullptr, m);
    }

    // Same-condition merge: ite(c, t1, e1) op ite(c, t2, e2) → ite(c, t1 op t2, e1 op e2)
    expr_ref derive::apply_ite(expr* c, expr* t1, expr* e1, expr* t2, expr* e2, std::function<expr_ref(expr*, expr*)> apply_op) {
        expr_ref then_br(m), else_br(m);
        switch (push(c, false)) {
        case l_true:  return apply_op(t1, t2);
        case l_undef: then_br = apply_op(t1, t2); pop(); break;
        case l_false: break;
        }
        switch (push(c, true)) {
        case l_true:  return apply_op(e1, e2);
        case l_undef: else_br = apply_op(e1, e2); pop(); break;
        case l_false: break;
        }
        if (then_br && else_br) return mk_ite(c, then_br, else_br);
        if (then_br) return then_br;
        if (else_br) return else_br;
        return expr_ref(nullptr, m);
    }

    // Unary apply_ite: hoist ite(c, t, e) through unary op with path pruning
    expr_ref derive::apply_ite(expr* c, expr* t, expr* e, std::function<expr_ref(expr*)> apply_op) {
        expr_ref then_br(m), else_br(m);
        switch (push(c, false)) {
        case l_true:  return apply_op(t);
        case l_undef: then_br = apply_op(t); pop(); break;
        case l_false: break;
        }
        switch (push(c, true)) {
        case l_true:  return apply_op(e);
        case l_undef: else_br = apply_op(e); pop(); break;
        case l_false: break;
        }
        if (then_br && else_br) return mk_ite(c, then_br, else_br);
        if (then_br) return then_br;
        if (else_br) return else_br;
        return expr_ref(nullptr, m);
    }

    // Push signed atoms onto m_path. Returns l_true if implied, l_false if contradicted, l_undef if pushed.
    lbool derive::push_path_atoms(expr* c, bool sign) {
        // Check if (c, sign) is already determined by the path
        for (auto const& [cond, csign] : m_path) {
            if (c == cond)
                return csign == sign ? l_true : l_false;
            expr* lhs1 = nullptr, * rhs1 = nullptr, * lhs2 = nullptr, * rhs2 = nullptr;
            if (!csign && m.is_eq(cond, lhs1, rhs1) && m.is_eq(c, lhs2, rhs2)) {
                if (m.is_value(lhs1)) std::swap(lhs1, rhs1);
                if (m.is_value(lhs2)) std::swap(lhs2, rhs2);
                if (lhs1 == lhs2 && m.are_distinct(rhs1, rhs2))
                    return sign ? l_true : l_false;
            }
        }

        // Composite: conjunction assumed true, or disjunction assumed false
        if (!sign && m.is_and(c)) {
            bool all_implied = true;
            for (expr* arg : *to_app(c)) {
                lbool r = push_path_atoms(arg, false);
                if (r == l_false) return l_false;
                if (r == l_undef) all_implied = false;
            }
            return all_implied ? l_true : l_undef;
        }
        if (sign && m.is_or(c)) {
            bool all_implied = true;
            for (expr* arg : *to_app(c)) {
                lbool r = push_path_atoms(arg, true);
                if (r == l_false) return l_false;
                if (r == l_undef) all_implied = false;
            }
            return all_implied ? l_true : l_undef;
        }

        // Atomic: push onto path
        m_path.push_back({ c, sign });
        return l_undef;
    }

    // Update m_intervals based on the condition. Returns l_true if implied, l_false if inconsistent, l_undef if pushed.
    lbool derive::push_intervals_impl(expr* c, bool sign) {
        unsigned lo = 0, hi = 0;
        bool negated = false;
        if (m_util.is_char_const_range(m_ele, c, lo, hi, negated)) {
            bool effective_neg = (negated != sign);
            if (!effective_neg) {
                if (lo <= hi) {
                    // Check if current intervals already imply [lo,hi]
                    bool already_subset = true;
                    for (auto const& [ilo, ihi] : m_intervals) {
                        if (ilo < lo || ihi > hi) { already_subset = false; break; }
                    }
                    if (already_subset) return l_true;
                    intersect_intervals(lo, hi, m_intervals);
                } else {
                    m_intervals.reset();
                }
            } else {
                if (lo <= hi) {
                    // Check if current intervals already exclude [lo,hi]
                    bool already_excluded = true;
                    for (auto const& [ilo, ihi] : m_intervals) {
                        if (ilo <= hi && ihi >= lo) { already_excluded = false; break; }
                    }
                    if (already_excluded) return l_true;
                    exclude_interval(lo, hi, m_intervals, u().max_char());
                }
            }
        } else if (!sign && m.is_and(c)) {
            bool all_implied = true;
            for (expr* arg : *to_app(c)) {
                lbool r = push_intervals_impl(arg, false);
                if (r == l_false) return l_false;
                if (r == l_undef) all_implied = false;
            }
            return all_implied ? l_true : (m_intervals.empty() ? l_false : l_undef);
        } else if (sign && m.is_or(c)) {
            bool all_implied = true;
            for (expr* arg : *to_app(c)) {
                lbool r = push_intervals_impl(arg, true);
                if (r == l_false) return l_false;
                if (r == l_undef) all_implied = false;
            }
            return all_implied ? l_true : (m_intervals.empty() ? l_false : l_undef);
        }
        return m_intervals.empty() ? l_false : l_undef;
    }

    // Evaluate a condition against the current path and intervals.
    lbool derive::eval_path_cond(expr* c) {
        // First try static evaluation (concrete m_ele, tautologies)
        lbool v = eval_cond(c);
        if (v != l_undef) return v;

        // Check against path atoms
        for (auto const& [cond, sign] : m_path) {
            if (c == cond)
                return sign ? l_false : l_true;
        }

        // Check against intervals
        v = eval_range_cond(m_intervals, c);
        if (v != l_undef) return v;

        // Check pred_implies from path atoms
        for (auto const& [cond, sign] : m_path) {
            if (pred_implies(sign, cond, false, c))
                return l_true;
            if (pred_implies(sign, cond, true, c))
                return l_false;
        }

        return l_undef;
    }

    // -------------------------------------------------------
    // Condition evaluation helpers
    // -------------------------------------------------------

    lbool derive::eval_cond(expr* cond) {
        expr* e1 = nullptr;

        if (m.is_true(cond)) return l_true;
        if (m.is_false(cond)) return l_false;

        // Use is_char_const_range to evaluate conditions involving m_ele
        unsigned lo = 0, hi = 0, ele_val = 0;
        bool negated = false;
        if (m_util.is_char_const_range(m_ele, cond, lo, hi, negated) && u().is_const_char(m_ele, ele_val)) {
            bool in_range = (lo <= ele_val && ele_val <= hi);
            return (in_range != negated) ? l_true : l_false;
        }

        // Handle self-equality and constant comparisons not involving m_ele
        expr* lhs = nullptr, * rhs = nullptr;
        if (m.is_eq(cond, lhs, rhs) && lhs == rhs)
            return l_true;

        unsigned vl = 0, vr = 0;
        if (u().is_char_le(cond, lhs, rhs)) {
            if (u().is_const_char(lhs, vl) && u().is_const_char(rhs, vr))
                return vl <= vr ? l_true : l_false;
            if (u().is_const_char(lhs, vl) && vl == 0)
                return l_true;
            if (u().is_const_char(rhs, vr) && vr == u().max_char())
                return l_true;
        }

        // not(e1)
        if (m.is_not(cond, e1))
            return ~eval_cond(e1);

        // and(...)
        if (m.is_and(cond)) {
            lbool r = l_true;
            for (expr* arg : *to_app(cond)) {
                lbool v = eval_cond(arg);
                if (v == l_false) return l_false;
                if (v == l_undef) r = l_undef;
            }
            return r;
        }

        // or(...)
        if (m.is_or(cond)) {
            lbool r = l_false;
            for (expr* arg : *to_app(cond)) {
                lbool v = eval_cond(arg);
                if (v == l_true) return l_true;
                if (v == l_undef) r = l_undef;
            }
            return r;
        }

        return l_undef;
    }

    lbool derive::eval_range_cond(intervals_t const& intervals, expr* c) {
        if (intervals.empty())
            return l_false;
        unsigned lo = 0, hi = 0;
        bool negated = false;
        if (!m_util.is_char_const_range(m_ele, c, lo, hi, negated))
            return l_undef;
        if (lo > hi) {
            return negated ? l_true : l_false;
        }
        // Check if [lo, hi] overlaps with intervals and/or contains all intervals
        bool any_overlap = false;
        bool all_contained = true;
        for (auto const& [r_lo, r_hi] : intervals) {
            if (std::max(r_lo, lo) <= std::min(r_hi, hi))
                any_overlap = true;
            if (r_lo < lo || r_hi > hi)
                all_contained = false;
        }
        if (!negated) {
            if (!any_overlap) return l_false;
            if (all_contained) return l_true;
        } else {
            if (all_contained) return l_false;
            if (!any_overlap) return l_true;
        }
        return l_undef;
    }

    void derive::intersect_intervals(unsigned lo, unsigned hi, intervals_t& ranges) {
        unsigned j = 0;
        for (unsigned i = 0; i < ranges.size(); ++i) {
            auto [lo1, hi1] = ranges[i];
            if (hi < lo1)
                break;
            if (hi1 >= lo)
                ranges[j++] = std::make_pair(std::max(lo1, lo), std::min(hi1, hi));
        }
        ranges.shrink(j);
    }

    void derive::exclude_interval(unsigned lo, unsigned hi, intervals_t& ranges, unsigned max_char) {
        if (lo == 0 && hi >= max_char) { ranges.reset(); return; }
        if (lo == 0) { intersect_intervals(hi + 1, max_char, ranges); return; }
        if (hi >= max_char) { intersect_intervals(0, lo - 1, ranges); return; }
        intervals_t right(ranges);
        intersect_intervals(0, lo - 1, ranges);
        intersect_intervals(hi + 1, max_char, right);
        ranges.append(right);
    }

}