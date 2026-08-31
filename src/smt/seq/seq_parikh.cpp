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
#include "util/obj_hashtable.h"
#include "util/zstring.h"
#include <algorithm>
#include <numeric>
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
            return std::gcd(mn, inner);
        }

        // r+ — one or more: same stride analysis as r*.
        if (seq.re.is_plus(re, r1)) {
            unsigned mn = seq.re.min_length(r1);
            unsigned inner = compute_length_stride(r1);
            return std::gcd(mn, inner);
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
                return std::gcd(mn, 0u);   // gcd(mn, 0) = mn; useful when mn > 1
            return std::gcd(inner, mn);
        }

        // concat(r1, r2): lengths add → stride = GCD(stride(r1), stride(r2)).
        if (seq.re.is_concat(re, r1, r2)) {
            unsigned s1 = compute_length_stride(r1);
            unsigned s2 = compute_length_stride(r2);
            return std::gcd(s1, s2);
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
            unsigned g = std::gcd(s1 == 0 ? d : s1, s2 == 0 ? d : s2);
            g = std::gcd(g, d);
            return g;
        }

        // loop(r, lo, hi): the length of any word is a sum of lo..hi copies of
        // lengths from L(r).  Since all lengths in L(r) are ≡ min_len(r) mod
        // stride(r), the overall stride is gcd(min_len(r), stride(r)).
        if (seq.re.is_loop(re, r1, lo, hi)) {
            unsigned mn = seq.re.min_length(r1);
            unsigned inner = compute_length_stride(r1);
            return std::gcd(mn, inner);
        }
        if (seq.re.is_loop(re, r1, lo)) {
            unsigned mn = seq.re.min_length(r1);
            unsigned inner = compute_length_stride(r1);
            return std::gcd(mn, inner);
        }

        // intersection(r1, r2): lengths must be in both languages.
        // A conservative safe choice: GCD(stride(r1), stride(r2)) is a valid
        // stride for the intersection (every length in the intersection is
        // also in r1 and in r2).
        if (seq.re.is_intersection(re, r1, r2)) {
            unsigned s1 = compute_length_stride(r1);
            unsigned s2 = compute_length_stride(r2);
            return std::gcd(s1, s2);
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

    // -----------------------------------------------------------------------
    // Per-letter Parikh abstraction, refined by length.  See seq_parikh.h.
    // -----------------------------------------------------------------------

    // Lengths are tracked as 0, 1 or "2 or more"; three classes per residue.
    static const unsigned LCAP = 2;

    static inline unsigned pbit(unsigned c, unsigned l) { return 1u << (c * 3 + l); }

    void seq_parikh::begin_pass(unsigned modulus, unsigned sigma) {
        SASSERT(2 <= modulus && modulus <= max_modulus);
        m_pk_mod = modulus;
        m_pk_sigma = sigma;
        m_pk_top = 0;
        for (unsigned c = 0; c < modulus; ++c)
            for (unsigned l = 0; l <= LCAP; ++l)
                m_pk_top |= pbit(c, l);
        m_pk_budget = 1 << 14;
        m_pk_prof.reset();
        m_pk_forced.reset();
    }

    unsigned seq_parikh::prof_cat(unsigned a1, unsigned a2) const {
        if (a1 == 0 || a2 == 0)
            return 0;
        unsigned r = 0;
        for (unsigned c1 = 0; c1 < m_pk_mod; ++c1)
            for (unsigned l1 = 0; l1 <= LCAP; ++l1) {
                if (!(a1 & pbit(c1, l1)))
                    continue;
                for (unsigned c2 = 0; c2 < m_pk_mod; ++c2)
                    for (unsigned l2 = 0; l2 <= LCAP; ++l2)
                        if (a2 & pbit(c2, l2))
                            r |= pbit((c1 + c2) % m_pk_mod, std::min(l1 + l2, LCAP));
            }
        return r;
    }

    // Binary exponentiation: the profile masks form a monoid under prof_cat
    // with unit {(0,0)}, so A^n is exact and costs O(log n) products.
    unsigned seq_parikh::prof_pow(unsigned a1, unsigned n) const {
        unsigned r = pbit(0, 0), base = a1;
        while (n > 0) {
            if (n & 1)
                r = prof_cat(r, base);
            n >>= 1;
            if (n > 0)
                base = prof_cat(base, base);
        }
        return r;
    }

    unsigned seq_parikh::prof_star(unsigned a1) const {
        unsigned r = pbit(0, 0);
        while (true) {
            const unsigned next = r | prof_cat(r, a1);
            if (next == r)
                return r;
            r = next;
        }
    }

    unsigned seq_parikh::prof_loop(unsigned a1, unsigned lo, unsigned hi) const {
        if (lo > hi)
            return 0;
        const unsigned base = prof_pow(a1, lo);
        // A^lo..A^hi is contained in A^lo · A*, which is cheap and sound; take it
        // whenever enumerating the exponents one by one would be the costlier of
        // the two.  The lattice has only 3·m elements, so nothing is lost.
        if (hi - lo > 3 * m_pk_mod)
            return prof_cat(base, prof_star(a1));
        unsigned r = 0, cur = base;
        for (unsigned i = lo; i <= hi; ++i) {
            r |= cur;
            cur = prof_cat(cur, a1);
        }
        return r;
    }

    unsigned seq_parikh::prof_chars(bool has_sigma, bool has_other) const {
        unsigned r = 0;
        if (has_sigma)
            r |= pbit(1 % m_pk_mod, 1);
        if (has_other)
            r |= pbit(0, 1);
        return r;
    }

    unsigned seq_parikh::forced(expr* re) {
        unsigned r = 0;
        if (m_pk_forced.find(re, r))
            return r;
        if (m_pk_budget == 0)
            return 0;               // sound: claim nothing is forced
        --m_pk_budget;

        expr* x = nullptr;
        zstring s;
        unsigned lo = 0, hi = 0;
        if (seq.re.is_full_seq(re))
            r = m_pk_top;
        else if (seq.re.is_full_char(re)) {
            // every one-character word belongs to allchar
            for (unsigned c = 0; c < m_pk_mod; ++c)
                r |= pbit(c, 1);
        }
        else if (seq.re.is_to_re(re, x) && seq.str.is_string(x, s)) {
            if (s.length() == 0)
                r = pbit(0, 0);                       // eps is the only word of profile (0,0)
            else if (s.length() == 1 && s[0] == m_pk_sigma)
                r = pbit(1 % m_pk_mod, 1);            // sigma is the only word of profile (1,1)
        }
        else if (seq.re.is_range(re, lo, hi)) {
            if (lo <= m_pk_sigma && m_pk_sigma <= hi)
                r = pbit(1 % m_pk_mod, 1);
        }
        else if (seq.re.is_union(re)) {
            for (expr* arg : *to_app(re))
                r |= forced(arg);
        }
        else if (seq.re.is_intersection(re)) {
            r = m_pk_top;
            for (expr* arg : *to_app(re))
                r &= forced(arg);
        }
        else if (seq.re.is_complement(re, x))
            r = m_pk_top & ~profiles(x);
        else if (seq.re.is_star(re, x) || seq.re.is_opt(re, x))
            r = forced(x) | pbit(0, 0);
        m_pk_forced.insert(re, r);
        return r;
    }

    unsigned seq_parikh::profiles(expr* re) {
        unsigned r = 0;
        if (m_pk_prof.find(re, r))
            return r;
        if (m_pk_budget == 0)
            return m_pk_top;        // sound: claim every profile is possible
        --m_pk_budget;

        expr* x = nullptr;
        expr* y = nullptr;
        zstring s;
        unsigned lo = 0, hi = 0;
        if (seq.re.is_empty(re))
            r = 0;
        else if (seq.re.is_full_seq(re))
            r = m_pk_top;
        else if (seq.re.is_full_char(re))
            r = prof_chars(true, true);
        else if (seq.re.is_to_re(re, x)) {
            if (seq.str.is_string(x, s)) {
                unsigned cnt = 0;
                for (unsigned i = 0; i < s.length(); ++i)
                    if (s[i] == m_pk_sigma)
                        ++cnt;
                r = pbit(cnt % m_pk_mod, std::min(s.length(), LCAP));
            }
            else
                r = m_pk_top;
        }
        else if (seq.re.is_concat(re)) {
            r = pbit(0, 0);
            for (expr* arg : *to_app(re)) {
                r = prof_cat(r, profiles(arg));
                if (r == 0)
                    break;
            }
        }
        else if (seq.re.is_union(re)) {
            for (expr* arg : *to_app(re))
                r |= profiles(arg);
        }
        else if (seq.re.is_intersection(re)) {
            r = m_pk_top;
            for (expr* arg : *to_app(re))
                r &= profiles(arg);
        }
        else if (seq.re.is_star(re, x))
            r = prof_star(profiles(x));
        else if (seq.re.is_plus(re, x)) {
            const unsigned p = profiles(x);
            r = prof_cat(p, prof_star(p));
        }
        else if (seq.re.is_opt(re, x))
            r = profiles(x) | pbit(0, 0);
        else if (seq.re.is_complement(re, x))
            r = m_pk_top & ~forced(x);
        else if (seq.re.is_diff(re, x, y))
            r = profiles(x) & (m_pk_top & ~forced(y));
        else if (seq.re.is_range(re, lo, hi)) {
            if (lo > hi)
                r = 0;              // SMT-LIB: an inverted range is the empty language
            else {
                const bool has_sigma = lo <= m_pk_sigma && m_pk_sigma <= hi;
                r = prof_chars(has_sigma, hi > lo || !has_sigma);
            }
        }
        else if (seq.re.is_loop(re, x, lo, hi))
            r = prof_loop(profiles(x), lo, hi);
        else if (seq.re.is_loop(re, x, lo)) {
            const unsigned p = profiles(x);
            r = prof_cat(prof_pow(p, lo), prof_star(p));
        }
        else
            r = m_pk_top;           // of_pred, reverse, derivative, ...
        m_pk_prof.insert(re, r);
        return r;
    }

    unsigned seq_parikh::regex_residues(expr* re, unsigned modulus, unsigned sigma) {
        if (modulus < 2 || modulus > max_modulus)
            return UINT_MAX;
        begin_pass(modulus, sigma);
        const unsigned mask = profiles(re);
        unsigned res = 0;
        for (unsigned c = 0; c < modulus; ++c)
            for (unsigned l = 0; l <= LCAP; ++l)
                if (mask & pbit(c, l)) {
                    res |= 1u << c;
                    break;
                }
        return res;
    }

    // -----------------------------------------------------------------------
    // Congruence refutation
    // -----------------------------------------------------------------------

    namespace {
        // constant + sum_x coeff[x] * n[x]  ==  some residue in m_mask  (mod m)
        struct pk_row {
            u_map<int>  m_coeff;
            int         m_const = 0;
            unsigned    m_mask = 0;
            dep_tracker m_dep = nullptr;
        };

        // Accumulate #sigma of a side: concrete tokens contribute to `cst`,
        // every other token is an opaque unknown keyed by its snode id.
        void scan_side(seq_util& seq, euf::snode const* side, unsigned sigma,
                       int sign, u_map<int>& coeff, int& cst) {
            euf::snode_vector toks;
            side->collect_tokens(toks);
            for (euf::snode const* t : toks) {
                expr* e = t->get_expr();
                zstring s;
                unsigned ch = 0;
                expr* u = nullptr;
                if (e && seq.str.is_string(e, s)) {
                    for (unsigned i = 0; i < s.length(); ++i)
                        if (s[i] == sigma)
                            cst += sign;
                }
                else if (e && seq.str.is_unit(e, u) && seq.is_const_char(u, ch)) {
                    if (ch == sigma)
                        cst += sign;
                }
                else {
                    const unsigned id = t->id();
                    coeff.insert_if_not_there(id, 0);
                    coeff[id] += sign;
                }
            }
        }

        // Gather the characters of an expression tree with multiplicity.
        void tally_chars(seq_util& seq, expr* e, u_map<unsigned>& freq) {
            if (!e)
                return;
            ptr_vector<expr> todo;
            obj_hashtable<expr> seen;
            todo.push_back(e);
            while (!todo.empty()) {
                expr* c = todo.back();
                todo.pop_back();
                if (seen.contains(c))
                    continue;
                seen.insert(c);
                zstring s;
                unsigned ch = 0;
                if (seq.str.is_string(c, s)) {
                    for (unsigned i = 0; i < s.length(); ++i) {
                        freq.insert_if_not_there(s[i], 0);
                        freq[s[i]]++;
                    }
                }
                else if (seq.is_const_char(c, ch)) {
                    freq.insert_if_not_there(ch, 0);
                    freq[ch]++;
                }
                if (is_app(c))
                    for (expr* arg : *to_app(c))
                        todo.push_back(arg);
            }
        }
    }

    void seq_parikh::collect_letters(nielsen_node const& node, unsigned max_letters,
                                     unsigned_vector& letters) {
        u_map<unsigned> freq;
        for (str_mem const& mem : node.str_mems()) {
            if (mem.m_regex)
                tally_chars(seq, mem.m_regex->get_expr(), freq);
            if (mem.m_str)
                tally_chars(seq, mem.m_str->get_expr(), freq);
        }
        for (str_eq const& eq : node.str_eqs()) {
            tally_chars(seq, eq.m_lhs->get_expr(), freq);
            tally_chars(seq, eq.m_rhs->get_expr(), freq);
        }
        svector<std::pair<unsigned, unsigned>> by_freq;   // (count, char)
        for (auto const& kv : freq)
            by_freq.push_back(std::make_pair(kv.m_value, kv.m_key));
        std::sort(by_freq.begin(), by_freq.end(),
                  [](std::pair<unsigned, unsigned> const& x,
                     std::pair<unsigned, unsigned> const& y) {
                      if (x.first != y.first)
                          return x.first > y.first;
                      return x.second < y.second;   // deterministic tie-break
                  });
        for (auto const& p : by_freq) {
            if (letters.size() >= max_letters)
                break;
            letters.push_back(p.second);
        }
    }

    bool seq_parikh::check_letter_conflict(nielsen_node const& node, dep_tracker& dep,
                                           unsigned max_mod, unsigned max_letters) {
        dep = nullptr;
        if (node.str_mems().empty())
            return false;           // the equation-only case is the abelian rule's
        if (max_mod > max_modulus)
            max_mod = max_modulus;

        unsigned_vector letters;
        collect_letters(node, max_letters, letters);
        if (letters.empty())
            return false;

        for (unsigned modulus = 2; modulus <= max_mod; ++modulus) {
            for (unsigned sigma : letters) {
                begin_pass(modulus, sigma);

                vector<pk_row> rows;
                bool constraining = false;
                const unsigned full = (modulus == 32) ? UINT_MAX : ((1u << modulus) - 1);

                for (str_mem const& mem : node.str_mems()) {
                    if (!mem.is_plain() || !mem.m_str || !mem.m_regex)
                        continue;
                    expr* re = mem.m_regex->get_expr();
                    if (!re || !seq.is_re(re))
                        continue;
                    const unsigned mask0 = profiles(re);
                    unsigned mask = 0;
                    for (unsigned c = 0; c < modulus; ++c)
                        for (unsigned l = 0; l <= LCAP; ++l)
                            if (mask0 & pbit(c, l)) {
                                mask |= 1u << c;
                                break;
                            }
                    if (mask == full)
                        continue;               // carries no information
                    constraining = true;
                    pk_row row;
                    row.m_mask = mask;
                    row.m_dep = mem.m_dep;
                    scan_side(seq, mem.m_str, sigma, 1, row.m_coeff, row.m_const);
                    rows.push_back(row);
                }
                if (!constraining)
                    continue;

                // Equations contribute the exact congruence #sigma(l) = #sigma(r).
                for (str_eq const& eq : node.str_eqs()) {
                    pk_row row;
                    row.m_mask = 1u;            // residue 0
                    row.m_dep = eq.m_dep;
                    scan_side(seq, eq.m_lhs, sigma, 1, row.m_coeff, row.m_const);
                    scan_side(seq, eq.m_rhs, sigma, -1, row.m_coeff, row.m_const);
                    rows.push_back(row);
                }

                // Unknowns actually occurring with a nonzero coefficient.
                unsigned_vector vars;
                u_map<unsigned> slot;
                for (pk_row const& row : rows)
                    for (auto const& kv : row.m_coeff) {
                        if (kv.m_value % (int) modulus == 0 || slot.contains(kv.m_key))
                            continue;
                        slot.insert(kv.m_key, vars.size());
                        vars.push_back(kv.m_key);
                    }

                // Enumerate Z_modulus ^ vars.  Bail out rather than blow up: the
                // rule is an optional filter, so giving up is always allowed.
                double space = 1;
                for (unsigned i = 0; i < vars.size(); ++i) {
                    space *= modulus;
                    if (space > 1e6)
                        break;
                }
                if (space > 1e6)
                    continue;

                // Precompute each row as a dense coefficient vector.
                vector<unsigned_vector> dense;
                unsigned_vector consts;
                for (pk_row const& row : rows) {
                    unsigned_vector v;
                    v.resize(vars.size(), 0);
                    for (auto const& kv : row.m_coeff) {
                        unsigned idx = 0;
                        if (slot.find(kv.m_key, idx)) {
                            int c = kv.m_value % (int) modulus;
                            if (c < 0)
                                c += modulus;
                            v[idx] = (unsigned) c;
                        }
                    }
                    dense.push_back(v);
                    int k = row.m_const % (int) modulus;
                    if (k < 0)
                        k += modulus;
                    consts.push_back((unsigned) k);
                }

                unsigned_vector asg;
                asg.resize(vars.size(), 0);
                bool feasible = false;
                const unsigned n = vars.size();
                while (true) {
                    bool ok = true;
                    for (unsigned i = 0; ok && i < rows.size(); ++i) {
                        unsigned t = consts[i];
                        unsigned_vector const& v = dense[i];
                        for (unsigned j = 0; j < n; ++j)
                            t += v[j] * asg[j];
                        ok = (rows[i].m_mask >> (t % modulus)) & 1;
                    }
                    if (ok) {
                        feasible = true;
                        break;
                    }
                    unsigned j = 0;
                    for (; j < n; ++j) {
                        if (++asg[j] < modulus)
                            break;
                        asg[j] = 0;
                    }
                    if (j == n)
                        break;
                }

                if (!feasible) {
                    for (pk_row const& row : rows)
                        dep = node.graph().dep_mgr().mk_join(dep, row.m_dep);
                    return true;
                }
            }
        }
        return false;
    }
} // namespace seq
