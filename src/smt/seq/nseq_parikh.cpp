/*++
Copyright (c) 2026 Microsoft Corporation

Module Name:

    nseq_parikh.cpp

Abstract:

    Parikh image filter implementation for the ZIPT-based Nielsen string
    solver.  See nseq_parith.h for the full design description.

    The key operation is compute_length_stride(re), which performs a
    structural traversal of the regex to find the period k such that all
    string lengths in L(re) are congruent to min_length(re) modulo k.
    The stride is used to generate modular length constraints that help
    the integer subsolver prune infeasible Nielsen graph nodes.

Author:

    Nikolaj Bjorner (nbjorner) 2026-03-10

--*/

#include "smt/seq/nseq_parith.h"
#include "ast/arith_decl_plugin.h"
#include "ast/seq_decl_plugin.h"
#include <string>

namespace seq {

    // -----------------------------------------------------------------------
    // Helpers
    // -----------------------------------------------------------------------

    // GCD via Euclidean algorithm.  gcd(0, x) = x, gcd(0, 0) = 0.
    unsigned nseq_parith::gcd(unsigned a, unsigned b) {
        if (a == 0 && b == 0) return 0;
        while (b != 0) {
            unsigned t = b;
            b = a % b;
            a = t;
        }
        return a;
    }

    nseq_parith::nseq_parith(euf::sgraph& sg)
        : m_sg(sg), m_fresh_cnt(0) {}

    expr_ref nseq_parith::mk_fresh_int_var() {
        ast_manager& m = m_sg.get_manager();
        arith_util arith(m);
        std::string name = "pk!" + std::to_string(m_fresh_cnt++);
        return expr_ref(m.mk_fresh_const(name.c_str(), arith.mk_int()), m);
    }

    // -----------------------------------------------------------------------
    // Stride computation
    // -----------------------------------------------------------------------

    // compute_length_stride: structural traversal of regex expression.
    //
    // Return value semantics:
    //   0 — fixed length (or empty language): no modular constraint needed
    //         beyond the min == max bounds.
    //   1 — all integer lengths ≥ min_len are achievable: no useful modular
    //         constraint.
    //   k > 1 — all lengths in L(re) satisfy len ≡ min_len (mod k):
    //         modular constraint len(str) = min_len + k·j is useful.
    unsigned nseq_parith::compute_length_stride(expr* re) {
        if (!re) return 1;

        seq_util& seq = m_sg.get_seq_util();
        expr* r1 = nullptr, *r2 = nullptr, *s = nullptr;
        unsigned lo = 0, hi = 0;

        // Empty language: no strings exist; stride is irrelevant.
        if (seq.re.is_empty(re))
            return 0;

        // Epsilon regex {""}: single fixed length 0.
        if (seq.re.is_epsilon(re))
            return 0;

        // to_re(concrete_string): fixed-length, no modular constraint needed.
        if (seq.re.is_to_re(re, s)) {
            // min_length == max_length, covered by bounds.
            return 0;
        }

        // Single character: range, full_char — fixed length 1.
        if (seq.re.is_range(re) || seq.re.is_full_char(re))
            return 0;

        // full_seq (.* / Σ*): every length ≥ 0 is possible.
        if (seq.re.is_full_seq(re))
            return 1;

        // r* — Kleene star.
        // L(r*) = {ε} ∪ L(r) ∪ L(r)·L(r) ∪ ...
        // If r has a fixed length k, then L(r*) = {0, k, 2k, ...} → stride k.
        // If r has variable length, strides from different iterations combine
        // by GCD.
        if (seq.re.is_star(re, r1)) {
            unsigned mn = seq.re.min_length(r1);
            unsigned mx = seq.re.max_length(r1);
            // When the body has unbounded length (mx == UINT_MAX), different
            // iterations can produce many different lengths, and the stride of
            // the star as a whole degenerates to gcd(mn, mn) = mn (or 1 if
            // mn == 1).  This is conservative: we use the body's min-length
            // as the only available fixed quantity.
            if (mx == UINT_MAX) mx = mn;
            if (mn == mx) {
                // Fixed-length body: L(r*) = {0, mn, 2·mn, ...} → stride = mn.
                // When mn == 1 the stride would be 1, which gives no useful
                // modular constraint, so return 0 instead.
                return (mn > 1) ? mn : 0;
            }
            // Variable-length body: GCD of min and max lengths
            return gcd(mn, mx);
        }

        // r+ — one or more: same stride analysis as r*.
        if (seq.re.is_plus(re, r1)) {
            unsigned mn = seq.re.min_length(r1);
            unsigned mx = seq.re.max_length(r1);
            if (mx == UINT_MAX) mx = mn;  // same conservative treatment as star
            if (mn == mx)
                return (mn > 1) ? mn : 0;
            return gcd(mn, mx);
        }

        // r? — zero or one: lengths = {0} ∪ lengths(r)
        // stride = GCD(mn_r, stride(r)) unless stride(r) is 0 (fixed length).
        if (seq.re.is_opt(re, r1)) {
            unsigned mn = seq.re.min_length(r1);
            unsigned inner = compute_length_stride(r1);
            // L(r?) includes length 0 and all lengths of L(r).
            // GCD(stride(r), min_len(r)) is a valid stride because:
            //   - the gap from 0 to min_len(r) is min_len(r) itself, and
            //   - subsequent lengths grow in steps governed by stride(r).
            // A result > 1 gives a useful modular constraint; result == 1
            // means every non-negative integer is achievable (no constraint).
            if (inner == 0)
                return gcd(mn, 0);   // gcd(mn, 0) = mn; useful when mn > 1
            return gcd(inner, mn);
        }

        // concat(r1, r2): lengths add → stride = GCD(stride(r1), stride(r2)).
        if (seq.re.is_concat(re, r1, r2)) {
            unsigned s1 = compute_length_stride(r1);
            unsigned s2 = compute_length_stride(r2);
            // 0 (fixed) on either side: result is governed by the other.
            if (s1 == 0 && s2 == 0) return 0;
            if (s1 == 0) return s2;
            if (s2 == 0) return s1;
            return gcd(s1, s2);
        }

        // union(r1, r2): lengths from either branch → need GCD of both
        // strides and the difference between their minimum lengths.
        if (seq.re.is_union(re, r1, r2)) {
            unsigned s1 = compute_length_stride(r1);
            unsigned s2 = compute_length_stride(r2);
            unsigned m1 = seq.re.min_length(r1);
            unsigned m2 = seq.re.min_length(r2);
            unsigned d  = (m1 >= m2) ? (m1 - m2) : (m2 - m1);
            // Replace 0-strides with d for GCD computation:
            // a fixed-length branch only introduces constraint via its offset.
            unsigned g = gcd(s1 == 0 ? d : s1, s2 == 0 ? d : s2);
            g = gcd(g, d);
            return g;
        }

        // loop(r, lo, hi): lengths = {lo·len(r), ..., hi·len(r)} if r is fixed.
        // stride = len(r) when r is fixed-length; otherwise GCD.
        if (seq.re.is_loop(re, r1, lo, hi)) {
            unsigned mn = seq.re.min_length(r1);
            unsigned mx = seq.re.max_length(r1);
            if (mx == UINT_MAX) mx = mn;
            if (mn == mx)
                return (mn > 1) ? mn : 0;
            return gcd(mn, mx);
        }
        if (seq.re.is_loop(re, r1, lo)) {
            unsigned mn = seq.re.min_length(r1);
            unsigned mx = seq.re.max_length(r1);
            if (mx == UINT_MAX) mx = mn;
            if (mn == mx)
                return (mn > 1) ? mn : 0;
            return gcd(mn, mx);
        }

        // intersection(r1, r2): lengths must be in both languages.
        // A conservative safe choice: GCD(stride(r1), stride(r2)) is a valid
        // stride for the intersection (every length in the intersection is
        // also in r1 and in r2).
        if (seq.re.is_intersection(re, r1, r2)) {
            unsigned s1 = compute_length_stride(r1);
            unsigned s2 = compute_length_stride(r2);
            if (s1 == 0 && s2 == 0) return 0;
            if (s1 == 0) return s2;
            if (s2 == 0) return s1;
            return gcd(s1, s2);
        }

        // For complement, diff, reverse, derivative, of_pred, and anything
        // else we cannot analyse statically: be conservative and return 1
        // (no useful modular constraint rather than an unsound one).
        return 1;
    }

    // -----------------------------------------------------------------------
    // Constraint generation
    // -----------------------------------------------------------------------

    void nseq_parith::generate_parikh_constraints(str_mem const& mem,
                                                   vector<int_constraint>& out) {
        if (!mem.m_regex || !mem.m_str)
            return;

        ast_manager& m = m_sg.get_manager();
        seq_util&    seq  = m_sg.get_seq_util();
        arith_util   arith(m);

        expr* re_expr = mem.m_regex->get_expr();
        if (!re_expr || !seq.is_re(re_expr))
            return;

        // Length bounds from the regex.
        unsigned min_len = seq.re.min_length(re_expr);
        unsigned max_len = seq.re.max_length(re_expr);

        // If min_len == max_len the bounds already pin the length exactly;
        // no modular constraint is needed.
        if (min_len == max_len)
            return;

        unsigned stride = compute_length_stride(re_expr);

        // stride == 1: every integer length is possible — no useful constraint.
        // stride == 0: fixed length or empty — handled by bounds.
        if (stride <= 1)
            return;

        // Build len(str) as an arithmetic expression.
        expr_ref len_str(seq.str.mk_length(mem.m_str->get_expr()), m);

        // Introduce fresh integer variable k ≥ 0.
        expr_ref k_var = mk_fresh_int_var();

        // Constraint 1: len(str) = min_len + stride · k
        expr_ref min_expr(arith.mk_int(min_len), m);
        expr_ref stride_expr(arith.mk_int(stride), m);
        expr_ref stride_k(arith.mk_mul(stride_expr, k_var), m);
        expr_ref rhs(arith.mk_add(min_expr, stride_k), m);
        out.push_back(int_constraint(len_str, rhs,
                                     int_constraint_kind::eq, mem.m_dep, m));

        // Constraint 2: k ≥ 0
        expr_ref zero(arith.mk_int(0), m);
        out.push_back(int_constraint(k_var, zero,
                                     int_constraint_kind::ge, mem.m_dep, m));
    }

    void nseq_parith::apply_to_node(nielsen_node& node) {
        vector<int_constraint> constraints;
        for (str_mem const& mem : node.str_mems())
            generate_parikh_constraints(mem, constraints);
        for (auto& ic : constraints)
            node.add_int_constraint(ic);
    }

} // namespace seq
