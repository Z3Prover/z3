/*++
Copyright (c) 2025 Microsoft Corporation

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

    Nikolaj Bjorner (nbjorner) 2025-06-03

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
        m_trail.reset();
    }

    expr_ref derive::operator()(expr* ele, expr* r) {
        SASSERT(m_util.is_re(r));
        if (m_trail.size() > 1000)
            reset();
        m_ele = ele;
        m_depth = 0;
        expr_ref result = derive_rec(r);
        result = simplify_ite(result);
        m_ele = nullptr;
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

    expr_ref derive::eval(expr* ele, expr* d) {
        expr_ref old_ele(m_ele, m);
        m_ele = ele;
        expr_ref result = simplify_ite(d);
        m_ele = old_ele;
        return result;
    }

    // -------------------------------------------------------
    // Core derivative computation
    // -------------------------------------------------------

    expr_ref derive::derive_rec(expr* r) {
        SASSERT(m_util.is_re(r));

        // Check cache
        expr* cached = nullptr;
        if (m_cache.find(r, cached))
            return expr_ref(cached, m);

        // Depth check
        if (m_depth >= m_max_depth) {
            // Return stuck derivative (the derivative operator applied symbolically)
            return expr_ref(re().mk_derivative(m_ele, r), m);
        }

        flet<unsigned> _scoped_depth(m_depth, m_depth + 1);
        expr_ref result = derive_core(r);

        // Cache the result
        m_cache.insert(r, result);
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
            if (norm)
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
            // ite(lo <= ele && ele <= hi, ε, ∅)
            expr_ref ge_lo(m_util.mk_le(c_lo, m_ele), m);
            expr_ref le_hi(m_util.mk_le(m_ele, c_hi), m);
            expr_ref in_range(m.mk_and(ge_lo, le_hi), m);
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
        return expr_ref(nullptr, m);
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

        // ITE combination: if both are ITE with same condition, merge
        expr *c1, *t1, *e1, *c2, *t2, *e2;
        if (m.is_ite(a, c1, t1, e1) && m.is_ite(b, c2, t2, e2) && c1 == c2) {
            expr_ref then_br = mk_union(t1, t2);
            expr_ref else_br = mk_union(e1, e2);
            return mk_ite(c1, then_br, else_br);
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

        // ITE combination: if both are ITE with same condition, merge
        expr *c1, *t1, *e1, *c2, *t2, *e2;
        if (m.is_ite(a, c1, t1, e1) && m.is_ite(b, c2, t2, e2) && c1 == c2) {
            expr_ref then_br = mk_inter(t1, t2);
            expr_ref else_br = mk_inter(e1, e2);
            return mk_ite(c1, then_br, else_br);
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

        return expr_ref(re().mk_complement(a), m);
    }

    expr_ref derive::mk_ite(expr* c, expr* t, expr* e) {
        if (m.is_true(c) || t == e)
            return expr_ref(t, m);
        if (m.is_false(c))
            return expr_ref(e, m);
        bool cond_val;
        if (eval_cond(c, cond_val))
            return cond_val ? expr_ref(t, m) : expr_ref(e, m);
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

    bool derive::eval_cond(expr* cond, bool& result) {
        expr* lhs = nullptr, * rhs = nullptr, * e1 = nullptr;
        unsigned ch1 = 0, ch2 = 0;

        if (m.is_true(cond)) { result = true; return true; }
        if (m.is_false(cond)) { result = false; return true; }

        // elem = char or char = elem
        if (m.is_eq(cond, lhs, rhs)) {
            if (rhs == m_ele) std::swap(lhs, rhs);
            if (lhs == m_ele && u().is_const_char(rhs, ch1) && u().is_const_char(m_ele, ch2)) {
                result = (ch1 == ch2);
                return true;
            }
            if (lhs == rhs) { result = true; return true; }
        }

        // char_le(lhs, rhs)
        if (u().is_char_le(cond, lhs, rhs)) {
            unsigned vl = 0, vr = 0;
            if (lhs == m_ele && u().is_const_char(m_ele, vl) && u().is_const_char(rhs, vr)) {
                result = (vl <= vr); return true;
            }
            if (rhs == m_ele && u().is_const_char(lhs, vl) && u().is_const_char(m_ele, vr)) {
                result = (vl <= vr); return true;
            }
            if (u().is_const_char(lhs, vl) && u().is_const_char(rhs, vr)) {
                result = (vl <= vr); return true;
            }
        }

        // not(e1)
        if (m.is_not(cond, e1)) {
            bool inner;
            if (eval_cond(e1, inner)) {
                result = !inner;
                return true;
            }
        }

        // and(...)
        if (m.is_and(cond)) {
            for (expr* arg : *to_app(cond)) {
                bool v;
                if (eval_cond(arg, v)) {
                    if (!v) { result = false; return true; }
                } else {
                    return false;
                }
            }
            result = true;
            return true;
        }

        // or(...)
        if (m.is_or(cond)) {
            for (expr* arg : *to_app(cond)) {
                bool v;
                if (eval_cond(arg, v)) {
                    if (v) { result = true; return true; }
                } else {
                    return false;
                }
            }
            result = false;
            return true;
        }

        return false;
    }

    expr_ref derive::simplify_ite(expr* d) {
        expr* c, * t, * e;
        if (!m.is_ite(d, c, t, e))
            return expr_ref(d, m);

        bool cond_val;
        if (eval_cond(c, cond_val))
            return simplify_ite(cond_val ? t : e);

        // Simplify branches with knowledge of the condition's truth value
        expr_ref st = simplify_ite_rec(c, false, t);
        expr_ref se = simplify_ite_rec(c, true, e);
        return mk_ite(c, st, se);
    }

    expr_ref derive::simplify_ite_rec(expr* cond, bool sign, expr* d) {
        expr* c, * t, * e;
        if (!m.is_ite(d, c, t, e))
            return expr_ref(d, m);

        // If the ITE condition matches cond directly
        if (c == cond)
            return sign ? simplify_ite(e) : simplify_ite(t);

        // If cond is (x = ch1) and c is (x = ch2) with ch1 != ch2:
        // when sign is false (cond is true, i.e., x = ch1), then c must be false
        expr* lhs1 = nullptr, * rhs1 = nullptr, * lhs2 = nullptr, * rhs2 = nullptr;
        if (!sign && m.is_eq(cond, lhs1, rhs1) && m.is_eq(c, lhs2, rhs2)) {
            if (u().is_const_char(lhs1)) std::swap(lhs1, rhs1);
            if (u().is_const_char(lhs2)) std::swap(lhs2, rhs2);
            unsigned ch1 = 0, ch2 = 0;
            if (lhs1 == lhs2 && u().is_const_char(rhs1, ch1) && u().is_const_char(rhs2, ch2) && ch1 != ch2)
                return simplify_ite_rec(cond, sign, e);
        }

        // General case: try to evaluate c given knowledge of cond
        bool cond_val;
        if (eval_cond(c, cond_val))
            return simplify_ite_rec(cond, sign, cond_val ? t : e);

        // Cannot simplify c: recurse into branches
        expr_ref st = simplify_ite_rec(cond, sign, t);
        expr_ref se = simplify_ite_rec(cond, sign, e);

        // Now also simplify c's branches with knowledge of c
        st = simplify_ite_rec(c, false, st);
        se = simplify_ite_rec(c, true, se);
        return mk_ite(c, st, se);
    }

}



