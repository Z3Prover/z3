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
        return true;
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

    // Find the integer q minimizing the weighted ell_1 cost
    //     f(q) = sum_r |H[r][j] - q*H[r][k]| + sum_i w_col[i] * |B[i][j] - q*B[i][k]|
    // and, if applying the corresponding column op strictly decreases f
    // (relative to q=0), perform it.  Sets improved = true on accept.
    // Returns false on bail (overflow).
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
        mpq cf = eval(qf);
        mpq cc = eval(qc);
        mpq c0 = eval(mpq(0));
        mpq best_q = qf;
        mpq best_c = cf;
        if (cc < best_c) { best_q = qc; best_c = cc; }
        if (best_c >= c0 || best_q.is_zero()) {
            // No strict improvement over q = 0 (identity).
            return true;
        }

        // Apply column op col_j <- col_j - q * col_k on H and B, and the
        // matching row op row_k <- row_k + q * row_j on B_inv.
        const mpq& q = best_q;
        for (unsigned r = 0; r < m; ++r) {
            mpq v = m_H[r][j] - q * m_H[r][k];
            if (too_big(v))
                return false;
            m_H[r][j] = v;
        }
        for (unsigned i = 0; i < n; ++i) {
            mpq v = m_B[i][j] - q * m_B[i][k];
            if (too_big(v))
                return false;
            m_B[i][j] = v;
        }
        for (unsigned c = 0; c < n; ++c) {
            mpq v = m_B_inv[k][c] + q * m_B_inv[j][c];
            if (too_big(v))
                return false;
            m_B_inv[k][c] = v;
        }
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
