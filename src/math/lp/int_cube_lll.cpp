/*++
Copyright (c) 2025 Microsoft Corporation

Module Name:

    int_cube_lll.cpp

Abstract:

    LLL-style cube heuristic. See int_cube_lll.h for the math.

Author:
    Lev Nachmanson (levnach)

Revision History:

--*/

#include "math/lp/int_cube_lll.h"
#include "math/lp/int_solver.h"
#include "math/lp/lar_solver.h"
#include <algorithm>

namespace lp {

    static const unsigned LLL_CUBE_LIMIT_ROWS = 75;
    static const unsigned LLL_CUBE_LIMIT_COLS = 150;
    static const unsigned LLL_CUBE_BITSIZE_LIMIT = 4096;
    static const unsigned LLL_CUBE_CANDIDATE_BITSIZE = 64;
    static const unsigned LLL_CUBE_MAX_PASSES = 8;

    int_cube_lll::int_cube_lll(int_solver& lia) : lia(lia), lra(lia.lra) {}

    bool int_cube_lll::too_big(const mpq& v) const {
        return v.bitsize() > LLL_CUBE_BITSIZE_LIMIT;
    }

    // For the delta=0 fast path on rows/columns with ||row||_1 <= 1 we need
    // both bounds (if present) to be integer-valued so that a rounded integer
    // y_p in the LP-feasible interval cannot escape [L, U].  Strict bounds
    // (non-zero y component) also disqualify the fast path.
    bool int_cube_lll::column_bounds_are_integral(unsigned j) const {
        if (lra.column_has_lower_bound(j)) {
            const impq& lb = lra.get_lower_bound(j);
            if (!is_zero(lb.y) || !lb.x.is_int())
                return false;
        }
        if (lra.column_has_upper_bound(j)) {
            const impq& ub = lra.get_upper_bound(j);
            if (!is_zero(ub.y) || !ub.x.is_int())
                return false;
        }
        return true;
    }

    // Collect J = { j : column_is_int(j) && !column_has_term(j) } and
    // m_term_js = { t.j() : t in lra.terms() && column_associated_with_row(t.j()) }.
    bool int_cube_lll::collect_J_and_terms() {
        m_J.reset();
        m_col_to_J.reset();
        m_col_to_J.resize(lra.column_count(), UINT_MAX);
        for (unsigned j = 0; j < lra.column_count(); ++j) {
            if (!lra.column_is_int(j))
                continue;
            if (lra.column_has_term(j))
                continue;
            m_col_to_J[j] = m_J.size();
            m_J.push_back(j);
        }
        if (m_J.empty())
            return false;
        if (m_J.size() > LLL_CUBE_LIMIT_COLS)
            return false;

        m_term_js.reset();
        for (const lar_term* t : lra.terms()) {
            if (!lra.column_associated_with_row(t->j()))
                continue;
            m_term_js.push_back(t->j());
        }
        if (m_term_js.size() > LLL_CUBE_LIMIT_ROWS)
            return false;
        return true;
    }

    // Build A in m_H and initialize B, B_inv to identity. Same as the HNF
    // variant: starts H = A, B = I.
    bool int_cube_lll::build_matrix() {
        unsigned m = m_term_js.size();
        unsigned n = m_J.size();
        m_H.reset();
        m_H.resize(m);
        for (unsigned r = 0; r < m; ++r)
            m_H[r].resize(n, mpq(0));

        for (unsigned r = 0; r < m; ++r) {
            const lar_term& t = lra.get_term(m_term_js[r]);
            for (lar_term::ival p : t) {
                if (p.j() >= m_col_to_J.size())
                    continue;
                unsigned k = m_col_to_J[p.j()];
                if (k == UINT_MAX)
                    continue;
                if (!p.coeff().is_int())
                    return false;
                if (too_big(p.coeff()))
                    return false;
                m_H[r][k] = p.coeff();
            }
        }
        m_B.reset();
        m_B.resize(n);
        m_B_inv.reset();
        m_B_inv.resize(n);
        for (unsigned i = 0; i < n; ++i) {
            m_B[i].resize(n, mpq(0));
            m_B_inv[i].resize(n, mpq(0));
            m_B[i][i] = mpq(1);
            m_B_inv[i][i] = mpq(1);
        }
        compute_col_weights();
        init_pair_invariants();
        return true;
    }

    // Cache per-row metadata, row 1-norms, and the identity-baseline cube
    // cost C(I).  Invariants of lra/bounds for the duration of operator(),
    // so we pay this once instead of per (j, k) reduce_pair call.
    void int_cube_lll::init_pair_invariants() {
        unsigned m = m_H.size();
        unsigned n = m_B.size();
        m_term_meta.reset();
        m_term_meta.resize(m);
        for (unsigned r = 0; r < m; ++r) {
            unsigned var = m_term_js[r];
            row_meta& meta = m_term_meta[r];
            meta.eligible = lra.column_has_lower_bound(var) && lra.column_has_upper_bound(var);
            if (meta.eligible) {
                meta.width = lra.get_upper_bound(var).x - lra.get_lower_bound(var).x;
                meta.integral_unit = column_bounds_are_integral(var);
            }
            else {
                meta.width = mpq(0);
                meta.integral_unit = false;
            }
        }
        m_col_meta.reset();
        m_col_meta.resize(n);
        for (unsigned i = 0; i < n; ++i) {
            unsigned var = m_J[i];
            row_meta& meta = m_col_meta[i];
            meta.eligible = lra.column_has_lower_bound(var) && lra.column_has_upper_bound(var);
            if (meta.eligible) {
                meta.width = lra.get_upper_bound(var).x - lra.get_lower_bound(var).x;
                meta.integral_unit = column_bounds_are_integral(var);
            }
            else {
                meta.width = mpq(0);
                meta.integral_unit = false;
            }
        }
        m_row_sum_H.reset();
        m_row_sum_H.resize(m, mpq(0));
        for (unsigned r = 0; r < m; ++r) {
            mpq s(0);
            for (unsigned c = 0; c < n; ++c)
                s += abs(m_H[r][c]);
            m_row_sum_H[r] = s;
        }
        m_row_sum_B.reset();
        m_row_sum_B.resize(n, mpq(0));
        for (unsigned i = 0; i < n; ++i) {
            mpq s(0);
            for (unsigned c = 0; c < n; ++c)
                s += abs(m_B[i][c]);
            m_row_sum_B[i] = s;
        }
        m_baseline_cost = mpq(0);
        for (unsigned r = 0; r < m; ++r)
            m_baseline_cost += m_row_sum_H[r];
        for (unsigned i = 0; i < n; ++i)
            m_baseline_cost += m_row_sum_B[i];
        m_total_cost = m_baseline_cost;
    }

    // Weight per column for the cube-cost function used by the greedy
    // basis reduction. A tight-box column (small ub - lb) is expensive
    // to grow because tightening by delta_col(j) >= (ub - lb)/2 would
    // collapse its box and bail.  We bias the greedy to keep row_j(B)
    // short on such columns by giving them a higher weight in the
    // sum_j w_j * ||row_j(B)||_1 part of the cost.
    //
    // Soundness is untouched: deltas used by tighten_columns_for_lll_cube
    // are still computed from ||row(B)||_1 in compute_deltas().
    void int_cube_lll::compute_col_weights() {
        unsigned n = m_J.size();
        m_col_w.reset();
        m_col_w.resize(n, mpq(1));
        for (unsigned i = 0; i < n; ++i) {
            unsigned j = m_J[i];
            if (!lra.column_has_lower_bound(j) || !lra.column_has_upper_bound(j))
                continue;
            const mpq& width = lra.get_upper_bound(j).x - lra.get_lower_bound(j).x;
            if (width <= mpq(0))
                continue;
            // w = max(1, 2/width).  width >= 2 keeps weight at 1;
            // width == 1 (tight integer column) gets weight 2.
            mpq two_over = mpq(2) / width;
            if (two_over > mpq(1))
                m_col_w[i] = two_over;
        }
    }

    // Find an integer q for the elementary column operation that first
    // reduces/avoids bound-collapse risk in the eventual tightening step, and
    // only then minimizes the weighted ell_1 cube cost.
    bool int_cube_lll::reduce_pair(unsigned j, unsigned k, bool& improved) {
        improved = false;
        unsigned m = m_H.size();
        unsigned n = m_B.size();

        // Gather breakpoints. Each (a, b, w) with b != 0 contributes
        //   w * |a - q*b| = w * |b| * |q - a/b|
        // to the cost; pairs with b == 0 contribute the constant w * |a|.
        struct bp { mpq a; mpq b; mpq w; };
        vector<bp> bps;
        bps.reserve(m + n);
        mpq constant_cost(0);
        for (unsigned r = 0; r < m; ++r) {
            const mpq& a = m_H[r][j];
            const mpq& b = m_H[r][k];
            if (b.is_zero()) {
                constant_cost += abs(a);
            } else {
                bps.push_back({a, b, mpq(1)});
            }
        }
        for (unsigned i = 0; i < n; ++i) {
            const mpq& a = m_B[i][j];
            const mpq& b = m_B[i][k];
            const mpq& w = m_col_w[i];
            if (b.is_zero()) {
                constant_cost += w * abs(a);
            } else {
                bps.push_back({a, b, w});
            }
        }
        if (bps.empty())
            return true;

        struct kv { mpq val; mpq w; };
        vector<kv> kvs;
        kvs.reserve(bps.size());
        for (auto& x : bps) {
            mpq w = x.w * abs(x.b);
            mpq v = x.a / x.b;
            kvs.push_back({v, w});
        }
        std::sort(kvs.begin(), kvs.end(),
                  [](const kv& a, const kv& b) { return a.val < b.val; });

        // Weighted median: the smallest val with prefix weight >= total / 2.
        mpq total(0);
        for (auto& x : kvs) total += x.w;
        mpq half = total * mpq(1, 2);
        mpq cum(0);
        mpq median(0);
        for (auto& x : kvs) {
            cum += x.w;
            if (cum >= half) { median = x.val; break; }
        }

        // Integer candidates: floor(median) and floor(median)+1. Evaluate
        // f at q = floor, q = floor+1, q = 0 and pick the smallest.
        auto eval = [&](const mpq& q) -> mpq {
            mpq c = constant_cost;
            for (auto& x : bps) {
                mpq d = x.a - q * x.b;
                c += x.w * abs(d);
            }
            return c;
        };
        mpq qf = floor(median);
        mpq qc = qf + mpq(1);

        // Risk rows are built in O(m + n) using cached metadata and the
        // maintained row 1-norms.  base(r, j) = ||row_r||_1 - |row_r[j]| is
        // the partial row sum that would survive the column-j update.
        struct risk_row {
            const row_meta* meta;
            mpq base;
            mpq a;
            mpq b;
        };
        vector<risk_row> risk_rows;
        risk_rows.reserve(m + n);
        for (unsigned r = 0; r < m; ++r) {
            const row_meta& meta = m_term_meta[r];
            if (!meta.eligible)
                continue;
            mpq base = m_row_sum_H[r] - abs(m_H[r][j]);
            risk_rows.push_back({&meta, base, m_H[r][j], m_H[r][k]});
        }
        for (unsigned i = 0; i < n; ++i) {
            const row_meta& meta = m_col_meta[i];
            if (!meta.eligible)
                continue;
            mpq base = m_row_sum_B[i] - abs(m_B[i][j]);
            risk_rows.push_back({&meta, base, m_B[i][j], m_B[i][k]});
        }

        auto row_excess = [](const risk_row& r, const mpq& q) {
            mpq norm = r.base + abs(r.a - q * r.b);
            if (norm.is_zero() || (norm == mpq(1) && r.meta->integral_unit))
                return mpq(0);
            return norm > r.meta->width ? norm - r.meta->width : mpq(0);
        };

        struct score {
            unsigned violations;
            mpq excess;
            mpq cost;
        };
        auto score_q = [&](const mpq& q) {
            score s = { 0, mpq(0), eval(q) };
            for (auto const& r : risk_rows) {
                mpq e = row_excess(r, q);
                if (!e.is_zero()) {
                    ++s.violations;
                    s.excess += e;
                }
            }
            return s;
        };

        auto better = [](const score& a, const score& b) {
            if (a.violations != b.violations)
                return a.violations < b.violations;
            if (a.excess != b.excess)
                return a.excess < b.excess;
            return a.cost < b.cost;
        };

        vector<mpq> candidates;
        // Cap candidate magnitude well below LLL_CUBE_BITSIZE_LIMIT so that
        // floor((a +/- width)/b) values for wide-box columns don't seed
        // basis growth and overflow downstream.
        auto add_candidate = [&](const mpq& q) {
            if (q.bitsize() > LLL_CUBE_CANDIDATE_BITSIZE)
                return;
            for (auto const& c : candidates)
                if (c == q)
                    return;
            candidates.push_back(q);
        };
        add_candidate(mpq(0));
        add_candidate(qf);
        add_candidate(qc);

        // If the current basis already collapses some boxes (typically term
        // rows inherited from A), also try q values that minimize the worst
        // offending rows.  This keeps the candidate set small while allowing
        // risk-reducing moves that are not at the weighted-cost median.
        vector<std::pair<mpq, unsigned>> risky;
        for (unsigned idx = 0; idx < risk_rows.size(); ++idx) {
            const risk_row& r = risk_rows[idx];
            if (!r.b.is_zero()) {
                mpq e = row_excess(r, mpq(0));
                if (!e.is_zero())
                    risky.push_back({e, idx});
            }
        }
        std::sort(risky.begin(), risky.end(),
                  [](const auto& a, const auto& b) { return a.first > b.first; });
        unsigned extra = std::min<unsigned>(4, risky.size());
        for (unsigned idx = 0; idx < extra; ++idx) {
            const risk_row& r = risk_rows[risky[idx].second];
            mpq center = r.a / r.b;
            mpq f = floor(center);
            add_candidate(f);
            add_candidate(f + mpq(1));
            mpq allowance = r.meta->width - r.base;
            if (allowance >= mpq(0)) {
                mpq lo = (r.a - allowance) / r.b;
                mpq hi = (r.a + allowance) / r.b;
                f = floor(lo);
                add_candidate(f);
                add_candidate(f + mpq(1));
                f = floor(hi);
                add_candidate(f);
                add_candidate(f + mpq(1));
            }
        }

        mpq best_q(0);
        score best = score_q(best_q);
        for (auto const& q : candidates) {
            score s = score_q(q);
            if (better(s, best)) {
                best = s;
                best_q = q;
            }
        }
        if (best_q.is_zero()) {
            // No strict lexicographic improvement over q = 0 (identity).
            return true;
        }

        // Apply column op col_j <- col_j - q * col_k on H and B, and the
        // matching row op row_k <- row_k + q * row_j on B_inv.  Update the
        // cached row 1-norms and running total cost in lock-step.
        const mpq& q = best_q;
        mpq delta_total(0);
        for (unsigned r = 0; r < m; ++r) {
            mpq old_a = m_H[r][j];
            mpq new_a = old_a - q * m_H[r][k];
            if (too_big(new_a))
                return false;
            m_H[r][j] = new_a;
            mpq d = abs(new_a) - abs(old_a);
            m_row_sum_H[r] += d;
            delta_total += d;
        }
        for (unsigned i = 0; i < n; ++i) {
            mpq old_a = m_B[i][j];
            mpq new_a = old_a - q * m_B[i][k];
            if (too_big(new_a))
                return false;
            m_B[i][j] = new_a;
            mpq d = abs(new_a) - abs(old_a);
            m_row_sum_B[i] += d;
            delta_total += d;
        }
        for (unsigned c = 0; c < n; ++c) {
            mpq v = m_B_inv[k][c] + q * m_B_inv[j][c];
            if (too_big(v))
                return false;
            m_B_inv[k][c] = v;
        }
        m_total_cost += delta_total;
        improved = true;
        return true;
    }

    // Monotone-safe greedy: start at B = I (so H = A) and accept only
    // strict improvements of cube cost.  At most LLL_CUBE_MAX_PASSES
    // sweeps over all ordered pairs; terminates earlier on a full
    // no-improvement pass.
    bool int_cube_lll::compute_basis() {
        unsigned n = m_B.size();
        if (n <= 1)
            return true;
        for (unsigned pass = 0; pass < LLL_CUBE_MAX_PASSES; ++pass) {
            bool any_improved_this_pass = false;
            for (unsigned j = 0; j < n; ++j) {
                for (unsigned k = 0; k < n; ++k) {
                    if (j == k)
                        continue;
                    bool improved = false;
                    if (!reduce_pair(j, k, improved))
                        return false;
                    if (improved)
                        any_improved_this_pass = true;
                }
            }
            if (!any_improved_this_pass)
                break;
        }
        return true;
    }

    void int_cube_lll::compute_deltas() {
        unsigned m = m_H.size();
        unsigned n = m_B.size();
        m_term_delta.reset();
        m_term_delta.resize(m);
        for (unsigned r = 0; r < m; ++r) {
            mpq s(0);
            for (unsigned k = 0; k < n; ++k)
                s += abs(m_H[r][k]);
            if (s.is_zero()) {
                m_term_delta[r] = impq(0);
            }
            else if (s == mpq(1) && column_bounds_are_integral(m_term_js[r])) {
                // Row of H has a single +1 entry: term value = +/- y_p, an
                // integer in lattice coords. With integer term bounds, no
                // shrinkage is needed.
                m_term_delta[r] = impq(0);
            }
            else {
                m_term_delta[r] = impq(s * mpq(1, 2));
            }
        }
        m_col_delta.reset();
        m_col_delta.resize(n);
        for (unsigned i = 0; i < n; ++i) {
            mpq s(0);
            for (unsigned k = 0; k < n; ++k)
                s += abs(m_B[i][k]);
            if (s.is_zero()) {
                m_col_delta[i] = impq(0);
            }
            else if (s == mpq(1) && column_bounds_are_integral(m_J[i])) {
                m_col_delta[i] = impq(0);
            }
            else {
                m_col_delta[i] = impq(s * mpq(1, 2));
            }
        }
    }

    bool int_cube_lll::tighten_terms_for_lll_cube() {
        for (unsigned r = 0; r < m_term_js.size(); ++r) {
            unsigned j = m_term_js[r];
            const impq& delta = m_term_delta[r];
            if (is_zero(delta))
                continue;
            if (!lra.tighten_term_bounds_by_delta(j, delta))
                return false;
        }
        return true;
    }

    bool int_cube_lll::tighten_column_bound_by_delta(unsigned j, const impq& delta) {
        SASSERT(!lra.column_has_term(j));
        if (is_zero(delta))
            return true;
        if (lra.column_has_upper_bound(j) && lra.column_has_lower_bound(j)) {
            if (lra.get_upper_bound(j) - delta < lra.get_lower_bound(j) + delta)
                return false;
        }
        if (lra.column_has_upper_bound(j)) {
            const impq& ub = lra.get_upper_bound(j);
            lconstraint_kind k = (!is_zero(delta.y) || !is_zero(ub.y)) ? LT : LE;
            lra.add_var_bound(j, k, ub.x - delta.x);
        }
        if (lra.column_has_lower_bound(j)) {
            const impq& lb = lra.get_lower_bound(j);
            lconstraint_kind k = (!is_zero(delta.y) || !is_zero(lb.y)) ? GT : GE;
            lra.add_var_bound(j, k, lb.x + delta.x);
        }
        return true;
    }

    bool int_cube_lll::tighten_columns_for_lll_cube() {
        for (unsigned i = 0; i < m_J.size(); ++i) {
            if (!tighten_column_bound_by_delta(m_J[i], m_col_delta[i]))
                return false;
        }
        return true;
    }

    void int_cube_lll::save_x_J() {
        unsigned n = m_J.size();
        m_saved_x_J.reset();
        m_saved_x_J.resize(n);
        for (unsigned i = 0; i < n; ++i)
            m_saved_x_J[i] = lra.get_column_value(m_J[i]);
    }

    void int_cube_lll::apply_rounding() {
        unsigned n = m_J.size();
        // Compute y* = B_inv * x_J* in impq (preserve infinitesimal y component).
        vector<impq> y(n, impq(0));
        for (unsigned i = 0; i < n; ++i) {
            impq s(0);
            for (unsigned k = 0; k < n; ++k)
                s += m_saved_x_J[k] * m_B_inv[i][k];
            y[i] = s;
        }
        // Round each y_i to the nearest integer using the same impq-aware rule
        // as lar_solver::round_to_integer_solution (lar_solver.cpp:2582-2589).
        for (unsigned i = 0; i < n; ++i) {
            impq const& v = y[i];
            impq flv(floor(v.x));
            impq del = flv - v;
            if (del < -impq(mpq(1, 2)))
                y[i] = impq(ceil(v.x));
            else
                y[i] = flv;
        }
        // z = B * y_round (now y has zero y-component since it's integer).
        vector<mpq> z(n, mpq(0));
        for (unsigned i = 0; i < n; ++i) {
            mpq s(0);
            for (unsigned k = 0; k < n; ++k)
                s += m_B[i][k] * y[k].x;
            z[i] = s;
        }
        // Push the new values into the LP and propagate to dependent terms.
        vector<std::pair<lpvar, impq>> assignments;
        for (unsigned i = 0; i < n; ++i) {
            unsigned j = m_J[i];
            impq new_val(z[i]);
            assignments.push_back({(lpvar)j, new_val});
        }
        lra.apply_lattice_assignment(assignments);
    }

    lia_move int_cube_lll::operator()() {
        lia.settings().stats().m_lll_cube_calls++;
        TRACE(lll_cube,
              for (unsigned j = 0; j < lra.number_of_vars(); ++j)
                  lia.display_column(tout, j);
              tout << lra.constraints();
            );

        if (!collect_J_and_terms()) {
            lia.settings().stats().m_lll_cube_bail_collect++;
            return lia_move::undef;
        }
        if (!build_matrix()) {
            lia.settings().stats().m_lll_cube_bail_build++;
            return lia_move::undef;
        }
        if (!compute_basis()) {
            lia.settings().stats().m_lll_cube_bail_basis++;
            return lia_move::undef;
        }
        // Monotonicity guard: bail if the computed basis did not strictly
        // improve the unweighted cube cost C(B) below the identity baseline
        // C(I) = ||A||_1 + n.  This restores the "never worse than plain
        // int_cube" guarantee that pre-lexicographic-scoring code provided.
        if (m_total_cost >= m_baseline_cost) {
            lia.settings().stats().m_lll_cube_bail_basis++;
            return lia_move::undef;
        }
        compute_deltas();

        lra.push();
        if (!tighten_terms_for_lll_cube()) {
            lia.settings().stats().m_lll_cube_bail_tighten++;
            lra.pop();
            lra.set_status(lp_status::OPTIMAL);
            return lia_move::undef;
        }
        if (!tighten_columns_for_lll_cube()) {
            lia.settings().stats().m_lll_cube_bail_tighten++;
            lra.pop();
            lra.set_status(lp_status::OPTIMAL);
            return lia_move::undef;
        }

        lp_status st = lra.find_feasible_solution();
        if (st != lp_status::FEASIBLE && st != lp_status::OPTIMAL) {
            lia.settings().stats().m_lll_cube_bail_infeasible++;
            TRACE(lll_cube, tout << "cannot find a feasible solution\n";);
            lra.pop();
            lra.move_non_basic_columns_to_bounds();
            if (!lra.r_basis_has_inf_int()) {
                lia.settings().stats().m_lll_cube_success_bail_sat++;
                return lia_move::sat;
            }
            return lia_move::undef;
        }
        save_x_J();
        lra.pop();
        apply_rounding();
        lra.set_status(lp_status::FEASIBLE);
        SASSERT(lia.settings().get_cancel_flag() || lia.is_feasible());
        TRACE(lll_cube, tout << "lll_cube success\n";);
        lia.settings().stats().m_lll_cube_success++;
        return lia_move::sat;
    }
}
