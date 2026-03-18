/*++
Copyright (c) 2026 Microsoft Corporation

Module Name:

    seq_parikh.cpp

Abstract:

    Parikh image filter implementation for the ZIPT-based Nielsen string
    solver.  See seq_parikh.h for the full design description.

    The key operation is compute_length_stride(re), which performs a
    structural traversal of the regex to find the period k such that all
    string lengths in L(re) are congruent to min_length(re) modulo k.
    The stride is used to generate modular length constraints that help
    the integer subsolver prune infeasible Nielsen graph nodes.

Author:

    Clemens Eisenhofer 2026-03-10
    Nikolaj Bjorner (nbjorner) 2026-03-10

--*/

#include "smt/seq/seq_parikh.h"
#include "util/mpz.h"
#include <string>

namespace seq {

    seq_parikh::seq_parikh(euf::sgraph& sg)
        : m(sg.get_manager()), seq(m), a(m), m_fresh_cnt(0) {}

    expr_ref seq_parikh::mk_fresh_int_var() {
        std::string name = "pk!" + std::to_string(m_fresh_cnt++);
        return expr_ref(m.mk_fresh_const(name.c_str(), a.mk_int()), m);
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
    unsigned seq_parikh::compute_length_stride(expr* re) {
        if (!re) return 1;

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
        // If all lengths in L(r) are congruent to c modulo s (c = min_len, s = stride),
        // then L(r*) includes lengths {0, c, c+s, 2c, 2c+s, 2c+2s, ...} and
        // the overall GCD is gcd(c, s).  This is strictly more accurate than
        // the previous gcd(min, max) approximation, which can be unsound when
        // the body contains lengths whose GCD is smaller than gcd(min, max).
        if (seq.re.is_star(re, r1)) {
            unsigned mn = seq.re.min_length(r1);
            unsigned inner = compute_length_stride(r1);
            // stride(r*) = gcd(min_length(r), stride(r))
            // when inner=0 (fixed-length body), gcd(mn, 0) = mn → stride = mn
            return u_gcd(mn, inner);
        }

        // r+ — one or more: same stride analysis as r*.
        if (seq.re.is_plus(re, r1)) {
            unsigned mn = seq.re.min_length(r1);
            unsigned inner = compute_length_stride(r1);
            return u_gcd(mn, inner);
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
                return u_gcd(mn, 0);   // gcd(mn, 0) = mn; useful when mn > 1
            return u_gcd(inner, mn);
        }

        // concat(r1, r2): lengths add → stride = GCD(stride(r1), stride(r2)).
        if (seq.re.is_concat(re, r1, r2)) {
            unsigned s1 = compute_length_stride(r1);
            unsigned s2 = compute_length_stride(r2);
            return u_gcd(s1, s2);
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
            unsigned g = u_gcd(s1 == 0 ? d : s1, s2 == 0 ? d : s2);
            g = u_gcd(g, d);
            return g;
        }

        // loop(r, lo, hi): the length of any word is a sum of lo..hi copies of
        // lengths from L(r).  Since all lengths in L(r) are ≡ min_len(r) mod
        // stride(r), the overall stride is gcd(min_len(r), stride(r)).
        if (seq.re.is_loop(re, r1, lo, hi)) {
            unsigned mn = seq.re.min_length(r1);
            unsigned inner = compute_length_stride(r1);
            return u_gcd(mn, inner);
        }
        if (seq.re.is_loop(re, r1, lo)) {
            unsigned mn = seq.re.min_length(r1);
            unsigned inner = compute_length_stride(r1);
            return u_gcd(mn, inner);
        }

        // intersection(r1, r2): lengths must be in both languages.
        // A conservative safe choice: GCD(stride(r1), stride(r2)) is a valid
        // stride for the intersection (every length in the intersection is
        // also in r1 and in r2).
        if (seq.re.is_intersection(re, r1, r2)) {
            unsigned s1 = compute_length_stride(r1);
            unsigned s2 = compute_length_stride(r2);
            return u_gcd(s1, s2);
        }

        // For complement, diff, reverse, derivative, of_pred, and anything
        // else we cannot analyse statically: be conservative and return 1
        // (no useful modular constraint rather than an unsound one).
        return 1;
    }

    // -----------------------------------------------------------------------
    // Constraint generation
    // -----------------------------------------------------------------------

    void seq_parikh::generate_parikh_constraints(str_mem const& mem,
                                                  vector<int_constraint>& out) {
        if (!mem.m_regex || !mem.m_str)
            return;

        expr* re_expr = mem.m_regex->get_expr();
        if (!re_expr || !seq.is_re(re_expr))
            return;

        // Length bounds from the regex.
        unsigned min_len = seq.re.min_length(re_expr);
        unsigned max_len = seq.re.max_length(re_expr);

        // If min_len >= max_len the bounds already pin the length exactly
        // (or the language is empty — empty language is detected by simplify_and_init
        // via Brzozowski derivative / is_empty checks, not here).
        // We only generate modular constraints when the length is variable.
        if (min_len >= max_len)
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
        expr_ref min_expr(a.mk_int(min_len), m);
        expr_ref stride_expr(a.mk_int(stride), m);
        expr_ref stride_k(a.mk_mul(stride_expr, k_var), m);
        expr_ref rhs(a.mk_add(min_expr, stride_k), m);
        out.push_back(int_constraint(len_str, rhs,
                                     int_constraint_kind::eq, mem.m_dep, m));

        // Constraint 2: k ≥ 0
        expr_ref zero(a.mk_int(0), m);
        out.push_back(int_constraint(k_var, zero,
                                     int_constraint_kind::ge, mem.m_dep, m));

        // Constraint 3 (optional): k ≤ max_k when max_len is bounded.
        // max_k = floor((max_len - min_len) / stride)
        // This gives the solver an explicit upper bound on k.
        // The subtraction is safe because min_len < max_len is guaranteed
        // by the early return above.
        if (max_len != UINT_MAX) {
            SASSERT(max_len > min_len);
            unsigned range = max_len - min_len;
            unsigned max_k = range / stride;
            expr_ref max_k_expr(a.mk_int(max_k), m);
            out.push_back(int_constraint(k_var, max_k_expr,
                                         int_constraint_kind::le, mem.m_dep, m));
        }
    }

    void seq_parikh::apply_to_node(nielsen_node& node) {
        vector<int_constraint> constraints;
        for (str_mem const& mem : node.str_mems())
            generate_parikh_constraints(mem, constraints);
        for (auto& ic : constraints)
            node.add_int_constraint(ic);
    }

    // -----------------------------------------------------------------------
    // Quick Parikh feasibility check (no solver call)
    // -----------------------------------------------------------------------

    // Returns true if a Parikh conflict is detected: there exists a membership
    // str ∈ re for a single-variable str where the modular length constraint
    //   len(str) = min_len + stride * k  (k ≥ 0)
    // is inconsistent with the variable's current integer bounds [lb, ub].
    //
    // This check is lightweight — it uses only modular arithmetic on the already-
    // known regex min/max lengths and the per-variable bounds stored in the node.
    bool seq_parikh::check_parikh_conflict(nielsen_node& node) {
        for (str_mem const& mem : node.str_mems()) {
            if (!mem.m_str || !mem.m_regex || !mem.m_str->is_var())
                continue;

            expr* re_expr = mem.m_regex->get_expr();
            if (!re_expr || !seq.is_re(re_expr))
                continue;

            unsigned min_len = seq.re.min_length(re_expr);
            unsigned max_len = seq.re.max_length(re_expr);
            if (min_len >= max_len) continue; // fixed or empty — no stride constraint

            unsigned stride = compute_length_stride(re_expr);
            if (stride <= 1) continue; // no useful modular constraint
            // stride > 1 guaranteed from here onward.
            SASSERT(stride > 1);

            unsigned lb = node.var_lb(mem.m_str);
            unsigned ub = node.var_ub(mem.m_str);

            // Check: ∃k ≥ 0 such that lb ≤ min_len + stride * k ≤ ub ?
            //
            // First find the smallest k satisfying the lower bound:
            //   k_min = 0                          if min_len ≥ lb
            //   k_min = ⌈(lb - min_len) / stride⌉  otherwise
            //
            // Then verify min_len + stride * k_min ≤ ub.
            unsigned k_min = 0;
            if (lb > min_len) {
                unsigned gap = lb - min_len;
                // Ceiling division: k_min = ceil(gap / stride).
                // Guard: (gap + stride - 1) may overflow if gap is close to UINT_MAX.
                // In that case k_min would be huge, and min_len + stride*k_min would
                // also overflow ub → treat as a conflict immediately.
                if (gap > UINT_MAX - (stride - 1)) {
                    return true; // ceiling division would overflow → k_min too large
                }
                k_min = (gap + stride - 1) / stride;
            }

            // Overflow guard: stride * k_min may overflow unsigned.
            unsigned len_at_k_min;
            if (k_min > (UINT_MAX - min_len) / stride) {
                // Overflow: min_len + stride * k_min > UINT_MAX ≥ ub → conflict.
                return true;
            }
            len_at_k_min = min_len + stride * k_min;

            if (ub != UINT_MAX && len_at_k_min > ub)
                return true; // no valid k exists → Parikh conflict
        }
        return false;
    }
} // namespace seq
