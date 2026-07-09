/*++
Copyright (c) 2026 Microsoft Corporation

Module Name:

    seq_parikh.cpp

Abstract:

    Parikh image filter implementation for the Nielsen string
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
#include "util/zstring.h"
#include <string>

namespace seq {

    seq_parikh::seq_parikh(euf::sgraph& sg)
        : m(sg.get_manager()), seq(m), a(m), m_rw(m), m_sk(m, m_rw), m_fresh_cnt(0) {}

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
    // Exact semi-linear length encoding (visit-count Parikh)
    // -----------------------------------------------------------------------

    expr_ref seq_parikh::mk_count_var(vector<constraint>& out, dep_tracker dep,
                                      expr* str_key, expr* root_re, unsigned& idx) {
        // Deterministic Skolem term keyed on the membership + a per-encoding DFS
        // index: re-encoding the same membership reuses the same counters.
        expr_ref c = m_sk.mk("seq.rc", str_key, root_re, a.mk_int(idx++), a.mk_int());
        out.push_back(constraint(a.mk_ge(c, a.mk_int(0)), dep, m));
        return c;
    }

    void seq_parikh::push_zero_guard(vector<constraint>& out, dep_tracker dep, expr* count, expr* c1) {
        // count = 0  ->  c1 = 0   (an unentered subterm produces nothing)
        expr_ref guard(m.mk_implies(m.mk_eq(count, a.mk_int(0)),
                                    m.mk_eq(c1, a.mk_int(0))), m);
        m_rw(guard);
        if (m.is_false(guard))
            return;
        out.push_back(constraint(guard, dep, m));
    }

    bool seq_parikh::rec(expr* re, expr* count, expr* str_key, expr* root_re, unsigned& idx,
                         dep_tracker dep, vector<constraint>& out, expr_ref& contrib) {
        SASSERT(re);
        contrib = expr_ref(a.mk_int(0), m);

        expr* r1 = nullptr, *r2 = nullptr, *s = nullptr;
        unsigned lo = 0, hi = 0;

        // ∅: this subterm can never be visited.
        if (seq.re.is_empty(re)) {
            out.push_back(constraint(m.mk_eq(count, a.mk_int(0)), dep, m));
            return true;
        }

        // ε: contributes no length.
        if (seq.re.is_epsilon(re))
            return true;

        // single character (range / allchar): one char per visit.
        if (seq.re.is_range(re) || seq.re.is_full_char(re)) {
            contrib = expr_ref(count, m);
            return true;
        }

        // to_re("w"): fixed-length literal → n chars per visit.
        if (seq.re.is_to_re(re, s)) {
            zstring zs;
            if (!seq.str.is_string(s, zs))
                return false; // symbolic to_re: not a classical length leaf
            unsigned n = zs.length();
            if (n != 0)
                contrib = expr_ref(a.mk_mul(a.mk_int(n), count), m);
            return true;
        }

        // Σ* (full_seq, incl. allchar*): any number of chars; gated by reachability.
        // NB: checked before is_star so star(allchar) is treated as Σ*.
        if (seq.re.is_full_seq(re)) {
            expr_ref c1 = mk_count_var(out, dep, str_key, root_re, idx);
            push_zero_guard(out, dep, count, c1);
            contrib = c1;
            return true;
        }

        // concat(r1, r2): both children visited exactly `count` times; lengths add.
        if (seq.re.is_concat(re, r1, r2)) {
            expr_ref l1(m), l2(m);
            if (!rec(r1, count, str_key, root_re, idx, dep, out, l1)) return false;
            if (!rec(r2, count, str_key, root_re, idx, dep, out, l2)) return false;
            contrib = expr_ref(a.mk_add(l1, l2), m);
            return true;
        }

        // union(r1, r2): each visit goes to exactly one branch: count = c1 + c2.
        if (seq.re.is_union(re, r1, r2)) {
            expr_ref c1 = mk_count_var(out, dep, str_key, root_re, idx);
            expr_ref c2 = mk_count_var(out, dep, str_key, root_re, idx);
            out.push_back(constraint(m.mk_eq(count, a.mk_add(c1, c2)), dep, m));
            expr_ref l1(m), l2(m);
            if (!rec(r1, c1, str_key, root_re, idx, dep, out, l1)) return false;
            if (!rec(r2, c2, str_key, root_re, idx, dep, out, l2)) return false;
            contrib = expr_ref(a.mk_add(l1, l2), m);
            return true;
        }

        // star(r1): body visited c1 >= 0 times total; reachability guard.
        if (seq.re.is_star(re, r1)) {
            expr_ref c1 = mk_count_var(out, dep, str_key, root_re, idx);
            push_zero_guard(out, dep, count, c1);
            return rec(r1, c1, str_key, root_re, idx, dep, out, contrib);
        }

        // plus(r1): >= 1 iteration per visit → c1 >= count; plus reachability guard.
        if (seq.re.is_plus(re, r1)) {
            expr_ref c1 = mk_count_var(out, dep, str_key, root_re, idx);
            out.push_back(constraint(a.mk_ge(c1, count), dep, m));
            push_zero_guard(out, dep, count, c1);
            return rec(r1, c1, str_key, root_re, idx, dep, out, contrib);
        }

        // opt(r1): 0 or 1 iteration per visit → c1 <= count (and c1 >= 0).
        if (seq.re.is_opt(re, r1)) {
            expr_ref c1 = mk_count_var(out, dep, str_key, root_re, idx);
            out.push_back(constraint(a.mk_le(c1, count), dep, m));
            return rec(r1, c1, str_key, root_re, idx, dep, out, contrib);
        }

        // loop(r1, lo, hi): between lo and hi iterations per visit.
        if (seq.re.is_loop(re, r1, lo, hi)) {
            expr_ref c1 = mk_count_var(out, dep, str_key, root_re, idx);
            out.push_back(constraint(a.mk_ge(c1, a.mk_mul(a.mk_int(lo), count)), dep, m));
            out.push_back(constraint(a.mk_le(c1, a.mk_mul(a.mk_int(hi), count)), dep, m));
            return rec(r1, c1, str_key, root_re, idx, dep, out, contrib);
        }
        // loop(r1, lo): at least lo iterations per visit, unbounded above.
        if (seq.re.is_loop(re, r1, lo)) {
            expr_ref c1 = mk_count_var(out, dep, str_key, root_re, idx);
            out.push_back(constraint(a.mk_ge(c1, a.mk_mul(a.mk_int(lo), count)), dep, m));
            push_zero_guard(out, dep, count, c1);
            return rec(r1, c1, str_key, root_re, idx, dep, out, contrib);
        }

        // intersection / complement / diff / xor / of_pred / reverse / derivative /
        // antimirov-union / anything else: the visit-count flow does not capture
        // these exactly — bail so the caller keeps the coarse fallback.
        return false;
    }

    bool seq_parikh::encode_length_set(expr* str_key, expr* re, expr* len_target, dep_tracker dep, vector<constraint>& out) {
        SASSERT(str_key && re && len_target && seq.is_re(re));
        unsigned before = out.size();
        unsigned idx = 0;
        expr_ref contrib(m);
        if (!rec(re, a.mk_int(1), str_key, re, idx, dep, out, contrib)) {
            out.shrink(before); // discard any partial constraints on bail
            return false;
        }
        out.push_back(constraint(m.mk_eq(len_target, contrib), dep, m));
        return true;
    }

    // -----------------------------------------------------------------------
    // Constraint generation
    // -----------------------------------------------------------------------

    void seq_parikh::generate_parikh_constraints(str_mem const& mem,
                                                  vector<constraint>& out) {
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
        out.push_back(constraint(m.mk_eq(len_str, rhs), mem.m_dep, m));

        // Constraint 2: k ≥ 0
        expr_ref zero(a.mk_int(0), m);
        out.push_back(constraint(a.mk_ge(k_var, zero), mem.m_dep, m));

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
            out.push_back(constraint(a.mk_le(k_var, max_k_expr), mem.m_dep, m));
        }
    }

    void seq_parikh::apply_to_node(nielsen_node& node) {
        vector<constraint> constraints;
        for (str_mem const& mem : node.str_mems()) {
            generate_parikh_constraints(mem, constraints);

            // Exact semi-linear length encoding for classical regex states.
            // Only plain memberships: view/guard kinds carry projection run
            // states, not plain regexes.  is_classical() pre-filters extended
            // ops (∩, complement, …); encode_length_set self-bails on anything
            // else (e.g. symbolic to_re) it cannot encode exactly.
            if (mem.is_plain() && mem.m_str && mem.m_regex && mem.m_regex->is_classical()
                && seq.is_re(mem.m_regex->get_expr())) {
                expr_ref len_str(seq.str.mk_length(mem.m_str->get_expr()), m);
                encode_length_set(mem.m_str->get_expr(), mem.m_regex->get_expr(), len_str, mem.m_dep, constraints);
            }
        }
        for (auto& ic : constraints)
            node.add_constraint(ic);
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
    str_mem const* seq_parikh::check_parikh_conflict(nielsen_node& node, dep_tracker& dep) {
        dep = nullptr;
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
            if (stride <= 1)
                continue; // no useful modular constraint
            // stride > 1 guaranteed from here onward.
            SASSERT(stride > 1);

            rational lb_r, ub_r;
            dep_tracker lb_dep = nullptr;
            dep_tracker ub_dep = nullptr;
            if (!node.lower_bound(mem.m_str->get_expr(), lb_r, lb_dep) ||
                !node.upper_bound(mem.m_str->get_expr(), ub_r, ub_dep))
                continue;

            dep_tracker cur_dep = node.graph().dep_mgr().mk_join(mem.m_dep, lb_dep);
            cur_dep = node.graph().dep_mgr().mk_join(cur_dep, ub_dep);

            SASSERT(lb_r <= ub_r);
            if (ub_r > INT_MAX)
                continue;

            const unsigned lb = (unsigned)lb_r.get_int32();
            const unsigned ub = (unsigned)ub_r.get_int32();

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
                    dep = cur_dep;
                    return &mem; // ceiling division would overflow → k_min too large
                }
                k_min = (gap + stride - 1) / stride;
            }

            // Overflow guard: stride * k_min may overflow unsigned.
            unsigned len_at_k_min;
            if (k_min > (UINT_MAX - min_len) / stride) {
                // Overflow: min_len + stride * k_min > UINT_MAX ≥ ub → conflict.
                dep = cur_dep;
                return &mem;
            }
            len_at_k_min = min_len + stride * k_min;

            if (ub != UINT_MAX && len_at_k_min > ub) {
                dep = cur_dep;
                return &mem; // no valid k exists → Parikh conflict
            }
        }
        return nullptr;
    }
} // namespace seq
