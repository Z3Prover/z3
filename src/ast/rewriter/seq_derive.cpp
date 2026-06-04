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
#include "ast/ast_pp.h"
#include "ast/array_decl_plugin.h"
#include "ast/rewriter/bool_rewriter.h"
#include "util/util.h"
#include <algorithm>

namespace seq {

    derive::derive(ast_manager& m) :
        m(m),
        m_util(m),
        m_autil(m),
        m_br(m),
        m_trail(m),
        m_ele(m) {
        m_br.set_flat_and_or(false);
    }

    void derive::reset() {
        m_cache.reset();
        m_top_cache.reset();
        m_trail.reset();
    }

    expr_ref derive::operator()(expr* ele, expr* r) {
        SASSERT(m_util.is_re(r));
        if (m_trail.size() > 1000)
            reset();
        // Check top-level cache (post-simplify result)
        expr* cached = nullptr;
        if (m_top_cache.find(ele, r, cached))
            return expr_ref(cached, m);
        m_ele = ele;
        m_depth = 0;
        expr_ref result = derive_rec(r);
        result = simplify_ite(result);
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

    // Lightweight structural subsumption: checks if L(a) ⊆ L(b)
    // Returns true only when subsumption can be determined structurally.
    bool derive::is_subset(expr* a, expr* b) {
        if (a == b) return true;
        if (re().is_empty(a)) return true;
        if (re().is_full_seq(b)) return true;

        // a ⊆ .+ iff a is non-nullable (non-nullable means ε ∉ L(a))
        expr* b1 = nullptr;
        if (re().is_plus(b, b1) && re().is_full_char(b1) &&
            re().get_info(a).nullable == l_false)
            return true;

        // a ⊆ a* (since a* accepts everything a does and more)
        if (re().is_star(b, b1) && a == b1) return true;

        // a* ⊆ b* if a ⊆ b
        expr* a1 = nullptr;
        if (re().is_star(a, a1) && re().is_star(b, b1) && is_subset(a1, b1)) return true;

        // a ⊆ b1 ∪ b2 if a ⊆ b1 or a ⊆ b2
        if (re().is_union(b, b1, a1)) {
            if (is_subset(a, b1) || is_subset(a, a1)) return true;
        }

        // a1 ∪ a2 ⊆ b if a1 ⊆ b and a2 ⊆ b
        if (re().is_union(a, a1, b1)) {
            if (is_subset(a1, b) && is_subset(b1, b)) return true;
        }

        // a1 ∩ a2 ⊆ b if a1 ⊆ b or a2 ⊆ b
        if (re().is_intersection(a, a1, b1)) {
            if (is_subset(a1, b) || is_subset(b1, b)) return true;
        }

        // a ⊆ b1 ∩ b2 if a ⊆ b1 and a ⊆ b2
        if (re().is_intersection(b, b1, a1)) {
            if (is_subset(a, b1) && is_subset(a, a1)) return true;
        }

        // concat subsumption: a1·a2 ⊆ b1·b2 when a1 ⊆ b1 and a2 ⊆ b2
        expr* a2 = nullptr, * b2 = nullptr;
        if (re().is_concat(a, a1, a2) && re().is_concat(b, b1, b2) && 
            is_subset(a1, b1) && is_subset(a2, b2))
            return true;

        // loop subsumption: r{la,ua} ⊆ r{lb,ub} when lb <= la and ua <= ub
        unsigned la, ua, lb, ub;
        if (re().is_loop(a, a1, la, ua) && re().is_loop(b, b1, lb, ub) &&
            a1 == b1 && lb <= la && ua <= ub)
            return true;

        // complement: ~a ⊆ ~b if b ⊆ a
        if (re().is_complement(a, a1) && re().is_complement(b, b1))
            return is_subset(b1, a1);

        return false;
    }

    expr_ref derive::mk_union(expr* a, expr* b) {
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

        // Subsumption: a ∪ b = b if a ⊆ b, a ∪ b = a if b ⊆ a
        if (is_subset(a, b)) return expr_ref(b, m);
        if (is_subset(b, a)) return expr_ref(a, m);

        // Prefix factoring: a·x ∪ a·y = a·(x ∪ y)
        expr *a1, *a2, *b1, *b2;
        if (re().is_concat(a, a1, a2) && re().is_concat(b, b1, b2) && a1 == b1) {
            expr_ref tail = mk_union(a2, b2);
            return mk_deriv_concat(expr_ref(a1, m), tail);
        }

        // ITE combination: if both are ITE with same condition, merge
        expr *c1, *t1, *e1, *c2, *t2, *e2;
        if (m.is_ite(a, c1, t1, e1) && m.is_ite(b, c2, t2, e2) && c1 == c2) {
            expr_ref then_br = mk_union(t1, t2);
            expr_ref else_br = mk_union(e1, e2);
            return mk_ite(c1, then_br, else_br);
        }

        // ITE hoisting: ite(c, t, e) ∪ r = ite(c, t ∪ r, e ∪ r)
        if (m.is_ite(a, c1, t1, e1)) {
            expr_ref then_br = mk_union(t1, b);
            expr_ref else_br = mk_union(e1, b);
            return mk_ite(c1, then_br, else_br);
        }
        if (m.is_ite(b, c2, t2, e2)) {
            expr_ref then_br = mk_union(a, t2);
            expr_ref else_br = mk_union(a, e2);
            return mk_ite(c2, then_br, else_br);
        }

        // ACI: flatten, sort, deduplicate
        expr_ref_vector args(m);
        flatten_union(a, args);
        flatten_union(b, args);

        // Sort by expr id for canonical form
        std::stable_sort(args.data(), args.data() + args.size(),
            [](expr* x, expr* y) { return x->get_id() < y->get_id(); });

        // Deduplicate
        unsigned j = 0;
        for (unsigned i = 0; i < args.size(); ++i) {
            if (j > 0 && args.get(i) == args.get(j - 1))
                continue; // skip duplicate
            if (re().is_empty(args.get(i)))
                continue; // skip empty
            if (re().is_full_seq(args.get(i)))
                return expr_ref(args.get(i), m); // universal absorbs
            args.set(j++, args.get(i));
        }
        args.shrink(j);

        if (args.empty())
            return expr_ref(re().mk_empty(a->get_sort()), m);

        return mk_union_from_sorted(args);
    }

    expr_ref derive::mk_inter(expr* a, expr* b) {
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

        // Subsumption: a ∩ b = a if a ⊆ b, a ∩ b = b if b ⊆ a
        if (is_subset(a, b)) return expr_ref(a, m);
        if (is_subset(b, a)) return expr_ref(b, m);

        // Prefix factoring: a·x ∩ a·y = a·(x ∩ y)
        expr *a1, *b1, *a2, *b2;
        if (re().is_concat(a, a1, a2) && re().is_concat(b, b1, b2) && a1 == b1) {
            expr_ref tail = mk_inter(a2, b2);
            return mk_deriv_concat(expr_ref(a1, m), tail);
        }

        // ITE combination: if both are ITE with same condition, merge
        expr *c1, *t1, *e1, *c2, *t2, *e2;
        if (m.is_ite(a, c1, t1, e1) && m.is_ite(b, c2, t2, e2) && c1 == c2) {
            expr_ref then_br = mk_inter(t1, t2);
            expr_ref else_br = mk_inter(e1, e2);
            return mk_ite(c1, then_br, else_br);
        }

        // ITE hoisting: ite(c, t, e) ∩ r = ite(c, t ∩ r, e ∩ r)
        if (m.is_ite(a, c1, t1, e1)) {
            expr_ref then_br = mk_inter(t1, b);
            expr_ref else_br = mk_inter(e1, b);
            return mk_ite(c1, then_br, else_br);
        }
        if (m.is_ite(b, c2, t2, e2)) {
            expr_ref then_br = mk_inter(a, t2);
            expr_ref else_br = mk_inter(a, e2);
            return mk_ite(c2, then_br, else_br);
        }

        // ACI: flatten, sort, deduplicate
        expr_ref_vector args(m);
        flatten_inter(a, args);
        flatten_inter(b, args);

        std::stable_sort(args.data(), args.data() + args.size(),
            [](expr* x, expr* y) { return x->get_id() < y->get_id(); });

        unsigned j = 0;
        for (unsigned i = 0; i < args.size(); ++i) {
            if (j > 0 && args.get(i) == args.get(j - 1))
                continue;
            if (re().is_full_seq(args.get(i)))
                continue; // skip universal
            if (re().is_empty(args.get(i)))
                return expr_ref(args.get(i), m); // empty absorbs
            args.set(j++, args.get(i));
        }
        args.shrink(j);

        if (args.empty())
            return expr_ref(re().mk_full_seq(a->get_sort()), m);

        // Special: r* ∩ .+ = r+
        expr* star_body = nullptr;
        int star_idx = -1, dotplus_idx = -1;
        for (unsigned i = 0; i < args.size(); ++i) {
            if (re().is_star(args.get(i), star_body))
                star_idx = i;
            if (re().is_dot_plus(args.get(i)))
                dotplus_idx = i;
        }
        if (star_idx >= 0 && dotplus_idx >= 0 && star_body) {
            args.set(star_idx, re().mk_plus(star_body));
            // Remove .+ by shifting
            for (unsigned i = dotplus_idx; i + 1 < args.size(); ++i)
                args.set(i, args.get(i + 1));
            args.shrink(args.size() - 1);
            if (args.size() == 1)
                return expr_ref(args.get(0), m);
        }

        return mk_inter_from_sorted(args);
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

        // Push through ITE: ~(ite(c, t, e)) → ite(c, ~t, ~e)
        expr* c, * t, * e;
        if (m.is_ite(a, c, t, e)) {
            expr_ref ct = mk_complement(t);
            expr_ref ce = mk_complement(e);
            return mk_ite(c, ct, ce);
        }

        // De Morgan: ~(r1 ∪ r2) → ~r1 ∩ ~r2
        expr* r1 = nullptr, * r2 = nullptr;
        if (re().is_union(a, r1, r2)) {
            expr_ref c1 = mk_complement(r1);
            expr_ref c2 = mk_complement(r2);
            return mk_inter(c1, c2);
        }

        // ~ε → .+
        sort* s = nullptr;
        if (re().is_to_re(a, r) && u().str.is_empty(r)) {
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
        lbool cond_val = eval_cond(c);
        if (cond_val == l_true) return expr_ref(t, m);
        if (cond_val == l_false) return expr_ref(e, m);
        return expr_ref(m.mk_ite(c, t, e), m);
    }

    // -------------------------------------------------------
    // ACI normalization helpers
    // -------------------------------------------------------

    void derive::flatten_union(expr* r, expr_ref_vector& args) {
        expr* a = nullptr, * b = nullptr;
        if (re().is_union(r, a, b)) {
            flatten_union(a, args);
            flatten_union(b, args);
        }
        else {
            args.push_back(r);
        }
    }

    void derive::flatten_inter(expr* r, expr_ref_vector& args) {
        expr* a = nullptr, * b = nullptr;
        if (re().is_intersection(r, a, b)) {
            flatten_inter(a, args);
            flatten_inter(b, args);
        }
        else {
            args.push_back(r);
        }
    }

    expr_ref derive::mk_union_from_sorted(expr_ref_vector& args) {
        if (args.empty()) {
            UNREACHABLE();
            return expr_ref(m.mk_true(), m);
        }
        if (args.size() == 1)
            return expr_ref(args.get(0), m);
        // Build right-associated union
        expr_ref result(args.back(), m);
        for (unsigned i = args.size() - 1; i-- > 0; )
            result = expr_ref(re().mk_union(args.get(i), result), m);
        return result;
    }

    expr_ref derive::mk_inter_from_sorted(expr_ref_vector& args) {
        if (args.empty()) {
            UNREACHABLE();
            return expr_ref(m.mk_true(), m);
        }
        if (args.size() == 1)
            return expr_ref(args.get(0), m);
        // Build right-associated intersection
        expr_ref result(args.back(), m);
        for (unsigned i = args.size() - 1; i-- > 0; )
            result = expr_ref(re().mk_inter(args.get(i), result), m);
        return result;
    }

    // -------------------------------------------------------
    // ITE-tree combinators (analogous to REsharp mk_binary/mk_unary)
    // -------------------------------------------------------

    expr_ref derive::ite_combine_binary(expr* d1, expr* d2,
        std::function<expr_ref(expr*, expr*)> const& op) {
        expr *c1, *t1, *e1, *c2, *t2, *e2;
        bool is_ite1 = m.is_ite(d1, c1, t1, e1);
        bool is_ite2 = m.is_ite(d2, c2, t2, e2);

        // Both are leaves (non-ITE)
        if (!is_ite1 && !is_ite2)
            return op(d1, d2);

        // d1 is ITE, d2 is not
        if (is_ite1 && !is_ite2) {
            expr_ref then_r = ite_combine_binary(t1, d2, op);
            expr_ref else_r = ite_combine_binary(e1, d2, op);
            return mk_ite(c1, then_r, else_r);
        }

        // d2 is ITE, d1 is not
        if (!is_ite1 && is_ite2) {
            expr_ref then_r = ite_combine_binary(d1, t2, op);
            expr_ref else_r = ite_combine_binary(d1, e2, op);
            return mk_ite(c2, then_r, else_r);
        }

        // Both are ITE
        if (c1 == c2) {
            // Same condition: combine pairwise
            expr_ref then_r = ite_combine_binary(t1, t2, op);
            expr_ref else_r = ite_combine_binary(e1, e2, op);
            return mk_ite(c1, then_r, else_r);
        }

        // Order by condition id (larger id on outside for canonical form)
        if (c1->get_id() > c2->get_id()) {
            expr_ref then_r = ite_combine_binary(t1, d2, op);
            expr_ref else_r = ite_combine_binary(e1, d2, op);
            return mk_ite(c1, then_r, else_r);
        }
        else {
            expr_ref then_r = ite_combine_binary(d1, t2, op);
            expr_ref else_r = ite_combine_binary(d1, e2, op);
            return mk_ite(c2, then_r, else_r);
        }
    }

    expr_ref derive::ite_combine_unary(expr* d,
        std::function<expr_ref(expr*)> const& op) {
        expr* c, * t, * e;
        if (m.is_ite(d, c, t, e)) {
            expr_ref then_r = ite_combine_unary(t, op);
            expr_ref else_r = ite_combine_unary(e, op);
            return mk_ite(c, then_r, else_r);
        }
        return op(d);
    }

    // -------------------------------------------------------
    // Distribute concat through ITE/union structure of derivative
    // -------------------------------------------------------

    expr_ref derive::mk_deriv_concat(expr* d, expr* tail) {
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
    // Post-processing: simplify ITE conditions w.r.t. m_ele
    // -------------------------------------------------------

    lbool derive::eval_cond(expr* cond) {
        expr* lhs = nullptr, * rhs = nullptr, * e1 = nullptr;
        unsigned ch1 = 0, ch2 = 0;

        if (m.is_true(cond)) return l_true;
        if (m.is_false(cond)) return l_false;

        // elem = char or char = elem
        if (m.is_eq(cond, lhs, rhs)) {
            if (rhs == m_ele) std::swap(lhs, rhs);
            if (lhs == m_ele && u().is_const_char(rhs, ch1) && u().is_const_char(m_ele, ch2))
                return ch1 == ch2 ? l_true : l_false;
            if (lhs == rhs) return l_true;
        }

        // char_le(lhs, rhs)
        if (u().is_char_le(cond, lhs, rhs)) {
            unsigned vl = 0, vr = 0;
            if (lhs == m_ele && u().is_const_char(m_ele, vl) && u().is_const_char(rhs, vr))
                return vl <= vr ? l_true : l_false;
            if (rhs == m_ele && u().is_const_char(lhs, vl) && u().is_const_char(m_ele, vr))
                return vl <= vr ? l_true : l_false;
            if (u().is_const_char(lhs, vl) && u().is_const_char(rhs, vr))
                return vl <= vr ? l_true : l_false;
            // char_le(0, x) is always true (chars are unsigned)
            if (u().is_const_char(lhs, vl) && vl == 0)
                return l_true;
            // char_le(x, max_char) is always true
            if (u().is_const_char(rhs, vr) && vr == u().max_char())
                return l_true;
        }

        // not(e1)
        if (m.is_not(cond, e1)) {
            lbool inner = eval_cond(e1);
            if (inner != l_undef)
                return inner == l_true ? l_false : l_true;
        }

        // and(...)
        if (m.is_and(cond)) {
            for (expr* arg : *to_app(cond)) {
                lbool v = eval_cond(arg);
                if (v == l_false) return l_false;
                if (v == l_undef) return l_undef;
            }
            return l_true;
        }

        // or(...)
        if (m.is_or(cond)) {
            for (expr* arg : *to_app(cond)) {
                lbool v = eval_cond(arg);
                if (v == l_true) return l_true;
                if (v == l_undef) return l_undef;
            }
            return l_false;
        }

        return l_undef;
    }

    // Evaluate a single atomic condition (char_le or equality) against path constraints.
    // Returns l_true if path implies cond, l_false if path contradicts cond, l_undef otherwise.
    lbool derive::eval_path_cond(path_t const& path, expr* c) {
        expr* c_lhs = nullptr, * c_rhs = nullptr;
        if (!m_util.is_char_le(c, c_lhs, c_rhs))
            return l_undef;

        unsigned c_lo = 0, c_hi = 0;
        for (auto const& [cond, sign] : path) {
            expr* p_lhs = nullptr, * p_rhs = nullptr;
            if (!m_util.is_char_le(cond, p_lhs, p_rhs))
                continue;
            unsigned p_lo = 0, p_hi = 0;
            if (sign) {
                // cond is negated: ¬cond is true
                // ¬(x <= hi) means x > hi, i.e., x >= hi+1
                if (p_lhs == m_ele && m_util.is_const_char(p_rhs, p_hi)) {
                    // We know x > p_hi (i.e., x >= p_hi+1)
                    // c is (lo <= x): if lo <= p_hi+1 → c is true (since x >= p_hi+1 >= lo)
                    if (m_util.is_const_char(c_lhs, c_lo) && c_rhs == m_ele && c_lo <= p_hi + 1)
                        return l_true;
                    // c is (x <= hi2): if hi2 <= p_hi → c is false (since x > p_hi >= hi2)
                    if (c_lhs == m_ele && m_util.is_const_char(c_rhs, c_hi) && c_hi <= p_hi)
                        return l_false;
                }
                // ¬(lo <= x) means x < lo, i.e., x <= lo-1
                if (m_util.is_const_char(p_lhs, p_lo) && p_rhs == m_ele && p_lo > 0) {
                    // We know x < p_lo (i.e., x <= p_lo-1)
                    // c is (x <= hi): if hi >= p_lo-1 → c is true (since x <= p_lo-1 <= hi)
                    if (c_lhs == m_ele && m_util.is_const_char(c_rhs, c_hi) && c_hi >= p_lo - 1)
                        return l_true;
                    // c is (lo <= x): if lo >= p_lo → c is false (since x < p_lo <= lo)
                    if (m_util.is_const_char(c_lhs, c_lo) && c_rhs == m_ele && c_lo >= p_lo)
                        return l_false;
                }
            } else {
                // cond is true (not negated)
                // (x <= hi) is true: we know x <= p_hi
                if (p_lhs == m_ele && m_util.is_const_char(p_rhs, p_hi)) {
                    // c is (lo <= x): if lo > p_hi → c is false (x <= p_hi < lo)
                    if (m_util.is_const_char(c_lhs, c_lo) && c_rhs == m_ele && c_lo > p_hi)
                        return l_false;
                    // c is (x <= hi2): if hi2 >= p_hi → c is true (x <= p_hi <= hi2)
                    if (c_lhs == m_ele && m_util.is_const_char(c_rhs, c_hi) && c_hi >= p_hi)
                        return l_true;
                }
                // (lo <= x) is true: we know x >= p_lo
                if (m_util.is_const_char(p_lhs, p_lo) && p_rhs == m_ele) {
                    // c is (x <= hi): if hi < p_lo → c is false (x >= p_lo > hi)
                    if (c_lhs == m_ele && m_util.is_const_char(c_rhs, c_hi) && c_hi < p_lo)
                        return l_false;
                    // c is (lo <= x): if lo <= p_lo → c is true (x >= p_lo >= lo)
                    if (m_util.is_const_char(c_lhs, c_lo) && c_rhs == m_ele && c_lo <= p_lo)
                        return l_true;
                }
            }
        }
        return l_undef;
    }

    void derive::push_path(path_t& path, expr* c, bool sign) {
        if (!sign && m.is_and(c)) {
            for (expr* arg : *to_app(c))
                push_path(path, arg, false);
        } else if (sign && m.is_or(c)) {
            for (expr* arg : *to_app(c))
                push_path(path, arg, true);
        } else {
            path.push_back({ c, sign });
        }
    }

    void derive::push_intervals(intervals_t& intervals, expr* c, bool sign) {
        expr* lhs = nullptr, * rhs = nullptr;
        unsigned val = 0;
        if (m_util.is_char_le(c, lhs, rhs)) {
            if (!sign) {
                if (lhs == m_ele && m_util.is_const_char(rhs, val))
                    intersect_intervals(0, val, intervals);
                else if (rhs == m_ele && m_util.is_const_char(lhs, val))
                    intersect_intervals(val, u().max_char(), intervals);
            } else {
                if (lhs == m_ele && m_util.is_const_char(rhs, val))
                    exclude_interval(0, val, intervals, u().max_char());
                else if (rhs == m_ele && m_util.is_const_char(lhs, val))
                    exclude_interval(val, u().max_char(), intervals, u().max_char());
            }
        } else if (!sign && m.is_and(c)) {
            for (expr* arg : *to_app(c))
                push_intervals(intervals, arg, false);
        } else if (sign && m.is_or(c)) {
            for (expr* arg : *to_app(c))
                push_intervals(intervals, arg, true);
        } else if (sign && m.is_and(c)) {
            // ¬(and(lo<=x, x<=hi)) → exclude [lo, hi]
            unsigned lo = 0, hi = u().max_char();
            bool got_lo = false, got_hi = false;
            for (expr* arg : *to_app(c)) {
                expr* a_lhs = nullptr, * a_rhs = nullptr;
                unsigned a_val = 0;
                if (m_util.is_char_le(arg, a_lhs, a_rhs)) {
                    if (a_lhs == m_ele && m_util.is_const_char(a_rhs, a_val))
                        { hi = std::min(hi, a_val); got_hi = true; }
                    else if (a_rhs == m_ele && m_util.is_const_char(a_lhs, a_val))
                        { lo = std::max(lo, a_val); got_lo = true; }
                }
            }
            if (got_lo || got_hi)
                exclude_interval(lo, hi, intervals, u().max_char());
        }
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

    lbool derive::eval_range_cond(intervals_t const& intervals, expr* c) {
        if (intervals.empty())
            return l_false;

        expr* lhs = nullptr, * rhs = nullptr;
        unsigned val = 0;

        // Handle AND of char_le as range [lo, hi]
        if (m.is_and(c)) {
            unsigned lo = 0, hi = u().max_char();
            bool got_lo = false, got_hi = false;
            bool all_char_le = true;
            for (expr* arg : *to_app(c)) {
                expr* a_lhs = nullptr, * a_rhs = nullptr;
                unsigned a_val = 0;
                if (m_util.is_char_le(arg, a_lhs, a_rhs)) {
                    if (a_lhs == m_ele && m_util.is_const_char(a_rhs, a_val))
                        { hi = std::min(hi, a_val); got_hi = true; }
                    else if (a_rhs == m_ele && m_util.is_const_char(a_lhs, a_val))
                        { lo = std::max(lo, a_val); got_lo = true; }
                    else all_char_le = false;
                } else all_char_le = false;
            }
            if (all_char_le && (got_lo || got_hi)) {
                if (lo > hi) return l_false;
                bool any_overlap = false;
                bool all_contained = true;
                for (auto const& [r_lo, r_hi] : intervals) {
                    if (std::max(r_lo, lo) <= std::min(r_hi, hi))
                        any_overlap = true;
                    if (r_lo < lo || r_hi > hi)
                        all_contained = false;
                }
                if (!any_overlap) return l_false;
                if (all_contained) return l_true;
            }
            return l_undef;
        }

        // Handle single char_le
        if (!m_util.is_char_le(c, lhs, rhs))
            return l_undef;

        if (lhs == m_ele && m_util.is_const_char(rhs, val)) {
            // c is (x <= val): true if all hi <= val, false if all lo > val
            bool all_le = true, any_le = false;
            for (auto const& [r_lo, r_hi] : intervals) {
                if (r_lo <= val) any_le = true;
                if (r_hi > val) all_le = false;
            }
            if (all_le) return l_true;
            if (!any_le) return l_false;
        } else if (rhs == m_ele && m_util.is_const_char(lhs, val)) {
            // c is (val <= x): true if all lo >= val, false if all hi < val
            bool all_ge = true, any_ge = false;
            for (auto const& [r_lo, r_hi] : intervals) {
                if (r_hi >= val) any_ge = true;
                if (r_lo < val) all_ge = false;
            }
            if (all_ge) return l_true;
            if (!any_ge) return l_false;
        }
        return l_undef;
    }

    std::pair<expr_ref, expr_ref> derive::simplify_ite_rec(path_t& path, intervals_t& intervals, expr* c, expr* t, expr* e) {
        auto sz = path.size();
        auto saved_intervals = intervals;
        push_path(path, c, false);
        push_intervals(intervals, c, false);
        expr_ref st = simplify_ite_rec(path, intervals, t);
        path.shrink(sz);
        intervals = saved_intervals;
        push_path(path, c, true);
        push_intervals(intervals, c, true);
        expr_ref se = simplify_ite_rec(path, intervals, e);
        path.shrink(sz);
        intervals = saved_intervals;
        return { st, se };
    }

    expr_ref derive::simplify_ite(expr* d) {
        expr* c, * t, * e;
        if (!m.is_ite(d, c, t, e))
            return expr_ref(d, m);

        lbool cond_val = eval_cond(c);
        if (cond_val == l_true) return simplify_ite(t);
        if (cond_val == l_false) return simplify_ite(e);

        path_t path;
        intervals_t intervals;
        intervals.push_back(std::make_pair(0u, u().max_char()));
        auto [st, se] = simplify_ite_rec(path, intervals, c, t, e);
        return mk_ite(c, st, se);
    }

    expr_ref derive::simplify_ite_rec(path_t& path, intervals_t& intervals, expr* d) {
        expr* c, * t, * e;
        if (!m.is_ite(d, c, t, e))
            return expr_ref(d, m);

        // Try to evaluate c directly
        lbool cond_val = eval_cond(c);
        if (cond_val == l_true) return simplify_ite_rec(path, intervals, t);
        if (cond_val == l_false) return simplify_ite_rec(path, intervals, e);

        // Use interval-based range reasoning (catches AND range vs disjoint intervals)
        lbool range_val = eval_range_cond(intervals, c);
        if (range_val == l_true) return simplify_ite_rec(path, intervals, t);
        if (range_val == l_false) return simplify_ite_rec(path, intervals, e);

        // When c is an AND (range condition), check each conjunct against the path.
        // If any conjunct is contradicted by the path, c is false → take else.
        // If all conjuncts are implied by the path, c is true → take then.
        if (m.is_and(c)) {
            lbool and_result = l_true;
            for (expr* arg : *to_app(c)) {
                lbool arg_val = eval_path_cond(path, arg);
                if (arg_val == l_false) {
                    and_result = l_false;
                    break;
                }
                if (arg_val == l_undef)
                    and_result = l_undef;
            }
            if (and_result == l_true) return simplify_ite_rec(path, intervals, t);
            if (and_result == l_false) return simplify_ite_rec(path, intervals, e);
        }
        // When c is a single char_le, also check against the path
        else {
            lbool c_val = eval_path_cond(path, c);
            if (c_val == l_true) return simplify_ite_rec(path, intervals, t);
            if (c_val == l_false) return simplify_ite_rec(path, intervals, e);
        }

        // Check if c can be determined from the path (legacy checks for equality conditions)
        for (auto const& [cond, sign] : path) {
            // Direct match: c == cond
            if (c == cond)
                return sign ? simplify_ite_rec(path, intervals, e) : simplify_ite_rec(path, intervals, t);

            // c is (x = v), cond is (x = w) with sign=false (cond is true, so x=w)
            // If v != w, then c is false → take else branch
            expr* lhs1 = nullptr, * rhs1 = nullptr, * lhs2 = nullptr, * rhs2 = nullptr;
            if (!sign && m.is_eq(cond, lhs1, rhs1) && m.is_eq(c, lhs2, rhs2)) {
                if (m.is_value(lhs1)) std::swap(lhs1, rhs1);
                if (m.is_value(lhs2)) std::swap(lhs2, rhs2);
                if (lhs1 == lhs2 && m.are_distinct(rhs1, rhs2))
                    return simplify_ite_rec(path, intervals, e);
            }

            // Range constraint: cond is (lo <= x) or (x <= hi) with sign=false
            // and c is (x = v). If v is outside the range, c is false.
            unsigned v_val = 0, lo_val = 0, hi_val = 0;
            if (!sign && m.is_eq(c, lhs2, rhs2)) {
                if (m.is_value(lhs2)) std::swap(lhs2, rhs2);
                if (m_util.is_const_char(rhs2, v_val)) {
                    expr* le_lhs = nullptr, * le_rhs = nullptr;
                    if (m_util.is_char_le(cond, le_lhs, le_rhs) && le_rhs == lhs2 &&
                        m_util.is_const_char(le_lhs, lo_val) && v_val < lo_val)
                        return simplify_ite_rec(path, intervals, e);
                    if (m_util.is_char_le(cond, le_lhs, le_rhs) && le_lhs == lhs2 &&
                        m_util.is_const_char(le_rhs, hi_val) && v_val > hi_val)
                        return simplify_ite_rec(path, intervals, e);
                }
            }

            // Range implication between char_le conditions:
            expr* c_lhs = nullptr, * c_rhs = nullptr;
            expr* p_lhs = nullptr, * p_rhs = nullptr;
            if (m_util.is_char_le(c, c_lhs, c_rhs) && m_util.is_char_le(cond, p_lhs, p_rhs)) {
                unsigned c_lo = 0, c_hi = 0, p_lo = 0, p_hi = 0;
                if (sign) {
                    if (m_util.is_const_char(c_lhs, c_lo) && c_rhs == m_ele &&
                        p_lhs == m_ele && m_util.is_const_char(p_rhs, p_hi) &&
                        c_lo <= p_hi + 1)
                        return simplify_ite_rec(path, intervals, t);
                    if (c_lhs == m_ele && m_util.is_const_char(c_rhs, c_hi) &&
                        m_util.is_const_char(p_lhs, p_lo) && p_rhs == m_ele &&
                        p_lo > 0 && p_lo - 1 <= c_hi)
                        return simplify_ite_rec(path, intervals, t);
                } else {
                    if (m_util.is_const_char(c_lhs, c_lo) && c_rhs == m_ele &&
                        p_lhs == m_ele && m_util.is_const_char(p_rhs, p_hi) &&
                        c_lo > p_hi)
                        return simplify_ite_rec(path, intervals, e);
                    if (c_lhs == m_ele && m_util.is_const_char(c_rhs, c_hi) &&
                        m_util.is_const_char(p_lhs, p_lo) && p_rhs == m_ele &&
                        c_hi < p_lo)
                        return simplify_ite_rec(path, intervals, e);
                    if (m_util.is_const_char(c_lhs, c_lo) && c_rhs == m_ele &&
                        m_util.is_const_char(p_lhs, p_lo) && p_rhs == m_ele &&
                        c_lo <= p_lo)
                        return simplify_ite_rec(path, intervals, t);
                    if (c_lhs == m_ele && m_util.is_const_char(c_rhs, c_hi) &&
                        p_lhs == m_ele && m_util.is_const_char(p_rhs, p_hi) &&
                        c_hi >= p_hi)
                        return simplify_ite_rec(path, intervals, t);
                }
            }
        }

        // Check if both range bounds are in path and c is (x = v) within range
        expr* lhs_c = nullptr, * rhs_c = nullptr;
        unsigned v_val = 0;
        if (m.is_eq(c, lhs_c, rhs_c)) {
            if (m.is_value(lhs_c)) std::swap(lhs_c, rhs_c);
            if (m_util.is_const_char(rhs_c, v_val)) {
                unsigned lo_bound = 0, hi_bound = UINT_MAX;
                bool has_lo = false, has_hi = false;
                for (auto const& [cond, sign] : path) {
                    if (sign) continue;
                    expr* le_lhs = nullptr, * le_rhs = nullptr;
                    if (m_util.is_char_le(cond, le_lhs, le_rhs)) {
                        unsigned bound = 0;
                        if (le_rhs == lhs_c && m_util.is_const_char(le_lhs, bound)) {
                            lo_bound = bound; has_lo = true;
                        }
                        if (le_lhs == lhs_c && m_util.is_const_char(le_rhs, bound)) {
                            hi_bound = bound; has_hi = true;
                        }
                    }
                }
                if (has_lo && has_hi && lo_bound <= v_val && v_val <= hi_bound) {
                    auto [st, se] = simplify_ite_rec(path, intervals, c, t, e);
                    return mk_ite(c, st, se);
                }
            }
        }

        // Cannot simplify c: recurse into branches with extended paths
        auto [st, se] = simplify_ite_rec(path, intervals, c, t, e);
        return mk_ite(c, st, se);
    }

}



