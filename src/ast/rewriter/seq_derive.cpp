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
        m_union_hoist_budget = 0;
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

        // Σ*-suffix subsumption: a ⊆ Σ*·B when a's right concat spine contains Σ*·B
        // Proof: if a = X·(Σ*·B), then L(a) = L(X)·L(Σ*·B). Every s in L(a) is
        // of the form p·t where t ∈ L(Σ*·B), meaning t has a suffix in L(B).
        // Therefore p·t also has that suffix, so p·t ∈ L(Σ*·B) = L(b).
        if (re().is_concat(b, b1, b2) && re().is_full_seq(b1)) {
            expr* cur = a;
            expr *l, *r;
            while (re().is_concat(cur, l, r)) {
                if (cur == b) return true;
                cur = r;
            }
            if (cur == b) return true;
            // Also check: a is a union and all members ⊆ b
            // (handled by the union check above, but double-check for nested concats)
        }

        // a ⊆ Σ*·B when a is a concat and its right spine contains b
        // (handles non-Σ*-starting concats too, via recursive check)
        if (re().is_concat(b, b1, b2) && re().is_full_seq(b1) && re().is_concat(a, a1, a2)) {
            // Check if the tail of a (a2) is a subset of b
            if (is_subset(a2, b)) return true;
        }

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

        // Negation: ~(range [a,b]) = [0,a-1] ∪ [b+1,max]
        // We don't handle negation here — it's handled via pred_implies logic
        if (m.is_not(cond, e1))
            return false;

        // Equality: ele == c → range [c, c]
        if (m.is_eq(cond, e1, e2)) {
            unsigned v;
            if (u().is_const_char(e1, v) && !u().is_const_char(e2, v)) {
                lo = hi = v;
                return true;
            }
            if (u().is_const_char(e2, v) && !u().is_const_char(e1, v)) {
                lo = hi = v;
                return true;
            }
            return false;
        }

        // Conjunction: and(char_le(lo, x), char_le(x, hi))
        if (m.is_and(cond, e1, e2)) {
            expr *a1, *a2, *b1, *b2;
            unsigned v;
            if (u().is_char_le(e1, a1, a2) && u().is_char_le(e2, b1, b2)) {
                // e1: a1 <= a2, e2: b1 <= b2
                // Expect: lo <= ele (a1=const, a2=var) and ele <= hi (b1=var, b2=const)
                // OR: ele <= hi (a1=var, a2=const) and lo <= ele (b1=const, b2=var)
                if (u().is_const_char(a1, v) && u().is_const_char(b2, lo)) {
                    // e1: const <= a2, e2: b1 <= const
                    // This is: v <= ele and ele <= lo — wrong naming, let me fix
                    lo = v;
                    hi = 0;
                    if (u().is_const_char(b2, hi))
                        return true;
                }
            }
            // Try more carefully: extract from each conjunct
            lo = 0;
            hi = u().max_char();
            if (u().is_char_le(e1, a1, a2)) {
                if (u().is_const_char(a1, v) && !u().is_const_char(a2, v))
                    lo = std::max(lo, v); // v <= ele
                else if (!u().is_const_char(a1, v) && u().is_const_char(a2, v))
                    hi = std::min(hi, v); // ele <= v
            }
            if (u().is_char_le(e2, b1, b2)) {
                unsigned v2;
                if (u().is_const_char(b1, v2) && !u().is_const_char(b2, v2))
                    lo = std::max(lo, v2); // v2 <= ele
                else if (!u().is_const_char(b1, v2) && u().is_const_char(b2, v2))
                    hi = std::min(hi, v2); // ele <= v2
            }
            return lo <= hi;
        }

        // Single char_le
        if (u().is_char_le(cond, lhs, rhs)) {
            unsigned v;
            if (u().is_const_char(lhs, v) && !u().is_const_char(rhs, v)) {
                lo = v; // v <= ele
                return true;
            }
            if (!u().is_const_char(lhs, v) && u().is_const_char(rhs, v)) {
                hi = v; // ele <= v
                return true;
            }
        }

        return false;
    }

    // Check if a condition is a recognizable character condition (or negation thereof)
    bool derive::is_char_cond(expr* c) {
        unsigned lo, hi;
        expr* e1;
        if (m.is_not(c, e1))
            return is_char_cond(e1);
        return extract_char_range(c, lo, hi);
    }

    // Predicate implication for character range conditions.
    // Returns true if: whenever cond_a is true, cond_b must also be true.
    // Used for BDD-merge of derivative ITE trees.
    bool derive::pred_implies(expr* a, expr* b) {
        if (a == b) return true;

        expr *nota = nullptr, *notb = nullptr;

        // ~a implies ~b  iff  b implies a
        if (m.is_not(a, nota) && m.is_not(b, notb))
            return pred_implies(notb, nota);

        unsigned lo_a, hi_a, lo_b, hi_b;

        // a implies b: range_a ⊆ range_b
        if (extract_char_range(a, lo_a, hi_a) && extract_char_range(b, lo_b, hi_b))
            return lo_b <= lo_a && hi_a <= hi_b;

        // a implies ~b: range_a ∩ range_b = ∅
        if (m.is_not(b, notb)) {
            if (extract_char_range(a, lo_a, hi_a) && extract_char_range(notb, lo_b, hi_b))
                return hi_a < lo_b || hi_b < lo_a;
        }

        // ~a implies b: complement of range_a ⊆ range_b
        // This is true when range_b covers everything outside range_a
        // i.e., lo_b == 0 and hi_b >= max_char, minus range_a... complex, skip for now
        if (m.is_not(a, nota)) {
            if (extract_char_range(nota, lo_a, hi_a) && extract_char_range(b, lo_b, hi_b))
                return lo_b <= 0 && hi_b >= u().max_char(); // only if b is universal
        }

        return false;
    }

    expr_ref derive::mk_union(expr* a, expr* b) {
        // Check op cache
        expr* cached = nullptr;
        if (m_union_cache.find(a, b, cached))
            return expr_ref(cached, m);

        expr_ref result = mk_union_core(a, b);

        // Store in cache
        m_union_cache.insert(a, b, result);
        m_trail.push_back(a);
        m_trail.push_back(b);
        m_trail.push_back(result);
        return result;
    }

    expr_ref derive::mk_union_core(expr* a, expr* b) {
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

        // ITE handling for union
        expr *c1, *t1, *e1, *c2, *t2, *e2;

        // Same condition merge (cheap, always correct)
        if (m.is_ite(a, c1, t1, e1) && m.is_ite(b, c2, t2, e2) && c1 == c2) {
            expr_ref then_br = mk_union(t1, t2);
            expr_ref else_br = mk_union(e1, e2);
            return mk_ite(c1, then_br, else_br);
        }

        // Budget-limited one-sided char-cond hoisting.
        // Enables BDD merge for small alphabets; budget caps work for large ones.
        if (m_union_hoist_budget < m_max_union_hoist_budget) {
            if (m.is_ite(a, c1, t1, e1) && is_char_cond(c1)) {
                ++m_union_hoist_budget;
                return mk_ite(c1, mk_union(t1, b), mk_union(e1, b));
            }
            if (m.is_ite(b, c2, t2, e2) && is_char_cond(c2)) {
                ++m_union_hoist_budget;
                return mk_ite(c2, mk_union(a, t2), mk_union(a, e2));
            }
        }

        // Conservative ITE hoisting via subsumption:
        // Only hoist when at least one branch simplifies by is_subset.
        // Skip expensive is_subset on branches that are themselves ITE trees.
        if (m.is_ite(a, c1, t1, e1)) {
            bool t1_sub_b = !m.is_ite(t1) && is_subset(t1, b);
            bool b_sub_t1 = !m.is_ite(t1) && !t1_sub_b && is_subset(b, t1);
            bool e1_sub_b = !m.is_ite(e1) && is_subset(e1, b);
            bool b_sub_e1 = !m.is_ite(e1) && !e1_sub_b && is_subset(b, e1);
            if (t1_sub_b || b_sub_t1 || e1_sub_b || b_sub_e1) {
                expr_ref then_br = t1_sub_b ? expr_ref(b, m) : b_sub_t1 ? expr_ref(t1, m) : mk_union(t1, b);
                expr_ref else_br = e1_sub_b ? expr_ref(b, m) : b_sub_e1 ? expr_ref(e1, m) : mk_union(e1, b);
                return mk_ite(c1, then_br, else_br);
            }
        }
        if (m.is_ite(b, c2, t2, e2)) {
            bool t2_sub_a = !m.is_ite(t2) && is_subset(t2, a);
            bool a_sub_t2 = !m.is_ite(t2) && !t2_sub_a && is_subset(a, t2);
            bool e2_sub_a = !m.is_ite(e2) && is_subset(e2, a);
            bool a_sub_e2 = !m.is_ite(e2) && !e2_sub_a && is_subset(a, e2);
            if (t2_sub_a || a_sub_t2 || e2_sub_a || a_sub_e2) {
                expr_ref then_br = t2_sub_a ? expr_ref(a, m) : a_sub_t2 ? expr_ref(t2, m) : mk_union(a, t2);
                expr_ref else_br = e2_sub_a ? expr_ref(a, m) : a_sub_e2 ? expr_ref(e2, m) : mk_union(a, e2);
                return mk_ite(c2, then_br, else_br);
            }
        }

        // BDD merge for union: only when both are ITE and pred_implies fires
        // (avoids exponential blowup when conditions are unrelated)
        if (m.is_ite(a, c1, t1, e1) && m.is_ite(b, c2, t2, e2)) {
            // Only merge if we can determine the relationship between conditions
            bool c1_imp_c2 = pred_implies(c1, c2);
            bool c1_imp_nc2 = !c1_imp_c2 && pred_implies(c1, m.mk_not(c2));
            expr_ref notc1(m.mk_not(c1), m);
            bool nc1_imp_c2 = pred_implies(notc1, c2);
            bool nc1_imp_nc2 = !nc1_imp_c2 && pred_implies(notc1, m.mk_not(c2));
            if (c1_imp_c2 || c1_imp_nc2 || nc1_imp_c2 || nc1_imp_nc2) {
                // pred_implies fires — safe to merge without exponential blowup
                expr_ref r1(m), r2(m);
                // Under c1:
                if (c1_imp_c2)
                    r1 = mk_union(t1, t2);
                else if (c1_imp_nc2)
                    r1 = mk_union(t1, e2);
                else
                    r1 = mk_union(t1, b);
                // Under ~c1:
                if (nc1_imp_c2)
                    r2 = mk_union(e1, t2);
                else if (nc1_imp_nc2)
                    r2 = mk_union(e1, e2);
                else
                    r2 = mk_union(e1, b);
                return mk_ite(c1, r1, r2);
            }
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
        // Check op cache
        expr* cached = nullptr;
        if (m_inter_cache.find(a, b, cached))
            return expr_ref(cached, m);

        expr_ref result = mk_inter_core(a, b);

        // Store in cache
        m_inter_cache.insert(a, b, result);
        m_trail.push_back(a);
        m_trail.push_back(b);
        m_trail.push_back(result);
        return result;
    }

    expr_ref derive::mk_inter_core(expr* a, expr* b) {
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

        // ITE handling for intersection
        expr *c1, *t1, *e1, *c2, *t2, *e2;

        // Same condition merge
        if (m.is_ite(a, c1, t1, e1) && m.is_ite(b, c2, t2, e2) && c1 == c2) {
            expr_ref then_br = mk_inter(t1, t2);
            expr_ref else_br = mk_inter(e1, e2);
            return mk_ite(c1, then_br, else_br);
        }

        // Both-ITE with pred_implies: exploit condition relationships (no depth cost)
        if (m.is_ite(a, c1, t1, e1) && m.is_ite(b, c2, t2, e2)) {
            // Order conditions: larger id on outside
            if (c1->get_id() < c2->get_id()) {
                std::swap(a, b);
                std::swap(c1, c2);
                std::swap(t1, t2);
                std::swap(e1, e2);
            }
            expr_ref r1(m), r2(m);
            bool have_r1 = false, have_r2 = false;
            // Under c1: what do we know about c2?
            if (pred_implies(c1, c2)) {
                r1 = mk_inter(t1, t2); have_r1 = true;
            } else if (pred_implies(c1, m.mk_not(c2))) {
                r1 = mk_inter(t1, e2); have_r1 = true;
            }
            // Under ~c1: what do we know about c2?
            expr_ref notc1(m.mk_not(c1), m);
            if (pred_implies(notc1, c2)) {
                r2 = mk_inter(e1, t2); have_r2 = true;
            } else if (pred_implies(notc1, m.mk_not(c2))) {
                r2 = mk_inter(e1, e2); have_r2 = true;
            }
            if (have_r1 || have_r2) {
                if (!have_r1) r1 = mk_inter(t1, b);
                if (!have_r2) r2 = mk_inter(e1, b);
                return mk_ite(c1, r1, r2);
            }
        }

        // ITE hoisting with depth bound (fallback when pred_implies doesn't fire)
        // Character conditions (recognizable ranges) get a larger depth allowance
        // since they form bounded BDD minterms for small alphabets.
        if (m.is_ite(a, c1, t1, e1)) {
            bool char_cond = is_char_cond(c1);
            unsigned max_depth = char_cond ? 8 : m_max_inter_hoist_depth;
            if (m_inter_hoist_depth < max_depth) {
                m_inter_hoist_depth++;
                expr_ref then_br = mk_inter(t1, b);
                expr_ref else_br = mk_inter(e1, b);
                m_inter_hoist_depth--;
                return mk_ite(c1, then_br, else_br);
            }
        }
        if (m.is_ite(b, c2, t2, e2)) {
            bool char_cond = is_char_cond(c2);
            unsigned max_depth = char_cond ? 8 : m_max_inter_hoist_depth;
            if (m_inter_hoist_depth < max_depth) {
                m_inter_hoist_depth++;
                expr_ref then_br = mk_inter(a, t2);
                expr_ref else_br = mk_inter(a, e2);
                m_inter_hoist_depth--;
                return mk_ite(c2, then_br, else_br);
            }
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
        // Check op cache
        expr* cached = nullptr;
        if (m_complement_cache.find(a, cached))
            return expr_ref(cached, m);

        expr_ref result = mk_complement_core(a);

        // Store in cache
        m_complement_cache.insert(a, result);
        m_trail.push_back(a);
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

        // Push through ITE: ~(ite(c, t, e)) → ite(c, ~t, ~e)
        // Only distribute if t or e is empty, full, or a complement
        // (avoids exponential blowup on complex ITE trees)
        expr* c, * t, * e;
        if (m.is_ite(a, c, t, e)) {
            if (re().is_empty(t) || re().is_full_seq(t) || re().is_complement(t) ||
                re().is_empty(e) || re().is_full_seq(e) || re().is_complement(e)) {
                expr_ref ct = mk_complement(t);
                expr_ref ce = mk_complement(e);
                return mk_ite(c, ct, ce);
            }
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
        // Remove subsumed elements: if a ⊆ b, drop a from union
        for (unsigned i = 0; i < args.size(); ++i) {
            for (unsigned j = 0; j < args.size(); ++j) {
                if (i != j && args.get(i) && args.get(j) && is_subset(args.get(i), args.get(j))) {
                    args[i] = args.back();
                    args.pop_back();
                    --i;
                    break;
                }
            }
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
        // Remove subsuming elements: if a ⊆ b, drop b from intersection
        for (unsigned i = 0; i < args.size(); ++i) {
            for (unsigned j = 0; j < args.size(); ++j) {
                if (i != j && args.get(i) && args.get(j) && is_subset(args.get(i), args.get(j))) {
                    args[j] = args.back();
                    args.pop_back();
                    if (j < i) --i;
                    --j;
                }
            }
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
    // Post-processing: simplify ITE conditions w.r.t. m_ele
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

    // Evaluate a single atomic condition (char_le or equality) against path constraints.
    // Returns l_true if path implies (c, !sign), l_false if path contradicts (c, !sign), l_undef otherwise.

    lbool derive::push_path(path_t& path, expr* c, bool sign) {
        // Check if (c, sign) is already determined by the path
        for (auto const& [cond, csign] : path) {
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

        // Composite case: conjunction (sign=false) or disjunction (sign=true)
        if (!sign && m.is_and(c)) {
            auto sz = path.size();
            lbool r = l_true;
            for (expr* arg : *to_app(c)) {
                lbool v = push_path(path, arg, false);
                if (v == l_false) { path.shrink(sz); return l_false; }
                if (v == l_undef) r = l_undef;
            }
            if (r == l_true) path.shrink(sz);
            return r;
        }
        if (sign && m.is_or(c)) {
            auto sz = path.size();
            lbool r = l_true;
            for (expr* arg : *to_app(c)) {
                lbool v = push_path(path, arg, true);
                if (v == l_false) { path.shrink(sz); return l_false; }
                if (v == l_undef) r = l_undef;
            }
            if (r == l_true) path.shrink(sz);
            return r;
        }

        // Atomic case: not determined, push onto path
        path.push_back({ c, sign });
        return l_undef;
    }

    lbool derive::push_intervals(intervals_t& intervals, expr* c, bool sign) {
        // First check if the condition is already determined by current intervals
        lbool range_val = eval_range_cond(intervals, c);
        if (range_val != l_undef)
            return sign ? ~range_val : range_val;

        // Not determined — modify intervals
        unsigned lo = 0, hi = 0;
        bool negated = false;
        if (m_util.is_char_const_range(m_ele, c, lo, hi, negated)) {
            bool effective_neg = (negated != sign);
            if (!effective_neg) {
                if (lo > hi)
                    return l_false;
                intersect_intervals(lo, hi, intervals);
            } else {
                if (lo <= hi)
                    exclude_interval(lo, hi, intervals, u().max_char());
            }
        } else if (!sign && m.is_and(c)) {
            auto saved = intervals;
            for (expr* arg : *to_app(c)) {
                lbool v = push_intervals(intervals, arg, false);
                if (v == l_false) { intervals = saved; return l_false; }
            }
        } else if (sign && m.is_or(c)) {
            auto saved = intervals;
            for (expr* arg : *to_app(c)) {
                lbool v = push_intervals(intervals, arg, true);
                if (v == l_false) { intervals = saved; return l_false; }
            }
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

    lbool derive::eval_range_cond(intervals_t const& intervals, expr* c) {
        if (intervals.empty())
            return l_false;
        unsigned lo = 0, hi = 0;
        bool negated = false;
        if (!m_util.is_char_const_range(m_ele, c, lo, hi, negated))
            return l_undef;
        if (lo > hi) {
            // c asserts x in empty range or c asserts x NOT in empty range
            return negated ? l_true : l_false;
        }
        // Check if [lo, hi] overlaps with intervals and/or contains all intervals
        bool any_overlap = false;
        bool all_contained = true; // all intervals ⊆ [lo, hi]
        for (auto const& [r_lo, r_hi] : intervals) {
            if (std::max(r_lo, lo) <= std::min(r_hi, hi))
                any_overlap = true;
            if (r_lo < lo || r_hi > hi)
                all_contained = false;
        }
        if (!negated) {
            // c asserts x ∈ [lo, hi]
            if (!any_overlap) return l_false;
            if (all_contained) return l_true;
        } else {
            // c asserts x ∉ [lo, hi]
            if (all_contained) return l_false; // all values are in [lo,hi], so ¬(x∈[lo,hi]) is false
            if (!any_overlap) return l_true;   // no values are in [lo,hi], so ¬(x∈[lo,hi]) is true
        }
        return l_undef;
    }

    std::pair<expr_ref, expr_ref> derive::simplify_ite_rec(path_t& path, intervals_t& intervals, expr* c, expr* t, expr* e, unsigned depth) {
        auto sz = path.size();
        auto saved_intervals = intervals;

        // Push c with sign=false (then-branch: c is true)
        lbool path_val = push_path(path, c, false);
        if (path_val != l_undef) {
            path.shrink(sz);
            expr_ref r = simplify_ite_rec(path, intervals, path_val == l_true ? t : e, depth);
            return { r, r };
        }

        lbool intv_val = push_intervals(intervals, c, false);
        if (intv_val != l_undef) {
            path.shrink(sz);
            intervals = saved_intervals;
            expr_ref r = simplify_ite_rec(path, intervals, intv_val == l_true ? t : e, depth);
            return { r, r };
        }

        // Then-branch increases depth
        expr_ref st = simplify_ite_rec(path, intervals, t, depth + 1);
        path.shrink(sz);
        intervals = saved_intervals;

        // Push c with sign=true (else-branch: c is false)
        path_val = push_path(path, c, true);
        if (path_val != l_undef) {
            path.shrink(sz);
            expr_ref r = simplify_ite_rec(path, intervals, path_val == l_true ? e : t, depth);
            return { r, r };
        }

        intv_val = push_intervals(intervals, c, true);
        if (intv_val != l_undef) {
            path.shrink(sz);
            intervals = saved_intervals;
            expr_ref r = simplify_ite_rec(path, intervals, intv_val == l_true ? e : t, depth);
            return { r, r };
        }

        // Else-branch does NOT increase depth (covers disjoint cases)
        expr_ref se = simplify_ite_rec(path, intervals, e, depth);
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
        auto [st, se] = simplify_ite_rec(path, intervals, c, t, e, 0);
        return mk_ite(c, st, se);
    }

    expr_ref derive::simplify_ite_rec(path_t& path, intervals_t& intervals, expr* d, unsigned depth) {
        expr* c, * t, * e;
        if (!m.is_ite(d, c, t, e))
            return expr_ref(d, m);

        // Depth limit reached — return without further simplification
        if (depth >= m_max_simp_depth)
            return expr_ref(d, m);

        // Try to evaluate c directly (handles trivially true/false conditions)
        lbool cond_val = eval_cond(c);
        if (cond_val == l_true) return simplify_ite_rec(path, intervals, t, depth);
        if (cond_val == l_false) return simplify_ite_rec(path, intervals, e, depth);

        // Cannot simplify c: recurse into branches with extended paths
        // push_path and push_intervals will check subsumption/contradiction
        auto [st, se] = simplify_ite_rec(path, intervals, c, t, e, depth);
        return mk_ite(c, st, se);
    }

}