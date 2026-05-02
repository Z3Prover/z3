/*++
Copyright (c) 2025 Microsoft Corporation

Module Name:

    int_cube_hnf.cpp

Abstract:

    HNF-cube finder.  See int_cube_hnf.h for the math.

Author:
    Lev Nachmanson (levnach)

Revision History:

--*/

#include "math/lp/int_cube_hnf.h"
#include "math/lp/int_solver.h"
#include "math/lp/lar_solver.h"
#include "math/lp/hnf.h"

namespace lp {

    static const unsigned HNF_CUBE_LIMIT_ROWS = 75;
    static const unsigned HNF_CUBE_LIMIT_COLS = 150;
    static const unsigned HNF_CUBE_BITSIZE_LIMIT = 4096;

    int_cube_hnf::int_cube_hnf(int_solver& lia) : lia(lia), lra(lia.lra) {}

    bool int_cube_hnf::too_big(const mpq& v) const {
        return v.bitsize() > HNF_CUBE_BITSIZE_LIMIT;
    }

    // For the delta=0 fast path on rows/columns with ||row||_1 <= 1 we need
    // both bounds (if present) to be integer-valued so that a rounded integer
    // y_p in the LP-feasible interval cannot escape [L, U].  Strict bounds
    // (non-zero y component) also disqualify the fast path.
    bool int_cube_hnf::column_bounds_are_integral(unsigned j) const {
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
    bool int_cube_hnf::collect_J_and_terms() {
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
        if (m_J.size() > HNF_CUBE_LIMIT_COLS)
            return false;

        m_term_js.reset();
        for (const lar_term* t : lra.terms()) {
            if (!lra.column_associated_with_row(t->j()))
                continue;
            m_term_js.push_back(t->j());
        }
        if (m_term_js.size() > HNF_CUBE_LIMIT_ROWS)
            return false;
        return true;
    }

    // Build A in m_H and initialize U, U_inv to identity.
    // Returns false if any term has a non-integer coefficient on a
    // J column (we conservatively bail) or if entries are too large.
    bool int_cube_hnf::build_matrix() {
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
        m_U.reset();
        m_U.resize(n);
        m_U_inv.reset();
        m_U_inv.resize(n);
        for (unsigned i = 0; i < n; ++i) {
            m_U[i].resize(n, mpq(0));
            m_U_inv[i].resize(n, mpq(0));
            m_U[i][i] = mpq(1);
            m_U_inv[i][i] = mpq(1);
        }
        return true;
    }

    // Column HNF on m_H tracking the column ops in m_U and the
    // matching row ops in m_U_inv.  Result: m_H = A * m_U,
    // m_U is unimodular, m_U_inv = m_U^{-1}.
    bool int_cube_hnf::compute_hnf() {
        unsigned m = m_H.size();
        unsigned n = m_U.size();
        unsigned pivot_col = 0;
        for (unsigned r = 0; r < m && pivot_col < n; ++r) {
            unsigned k_nz = UINT_MAX;
            for (unsigned k = pivot_col; k < n; ++k) {
                if (!m_H[r][k].is_zero()) { k_nz = k; break; }
            }
            if (k_nz == UINT_MAX)
                continue;
            if (k_nz != pivot_col) {
                for (unsigned i = 0; i < m; ++i)
                    std::swap(m_H[i][pivot_col], m_H[i][k_nz]);
                for (unsigned i = 0; i < n; ++i)
                    std::swap(m_U[i][pivot_col], m_U[i][k_nz]);
                std::swap(m_U_inv[pivot_col], m_U_inv[k_nz]);
            }

            // Eliminate H[r][k] for k > pivot_col using extended_gcd.
            for (unsigned k = pivot_col + 1; k < n; ++k) {
                if (m_H[r][k].is_zero())
                    continue;
                mpq a = m_H[r][pivot_col];
                mpq b = m_H[r][k];
                mpq d, x, y;
                hnf_calc::extended_gcd_minimal_uv(a, b, d, x, y);
                if (too_big(d) || too_big(x) || too_big(y))
                    return false;
                mpq a_over_d = a / d;
                mpq b_over_d = b / d;
                if (too_big(a_over_d) || too_big(b_over_d))
                    return false;
                // Column op: col_p' = x * col_p + y * col_k,
                //            col_k' = -b/d * col_p + a/d * col_k.
                // det of the 2x2 elementary = (x*a + y*b) / d = 1.
                for (unsigned i = 0; i < m; ++i) {
                    mpq h_p = m_H[i][pivot_col];
                    mpq h_k = m_H[i][k];
                    mpq new_p = x * h_p + y * h_k;
                    mpq new_k = -b_over_d * h_p + a_over_d * h_k;
                    if (too_big(new_p) || too_big(new_k))
                        return false;
                    m_H[i][pivot_col] = new_p;
                    m_H[i][k] = new_k;
                }
                for (unsigned i = 0; i < n; ++i) {
                    mpq u_p = m_U[i][pivot_col];
                    mpq u_k = m_U[i][k];
                    mpq new_p = x * u_p + y * u_k;
                    mpq new_k = -b_over_d * u_p + a_over_d * u_k;
                    if (too_big(new_p) || too_big(new_k))
                        return false;
                    m_U[i][pivot_col] = new_p;
                    m_U[i][k] = new_k;
                }
                // Inverse of the elementary 2x2 [[x, -b/d], [y, a/d]] is
                // [[a/d, b/d], [-y, x]].  Apply as a row op on U_inv:
                //   row_p' =  a/d * row_p + b/d * row_k
                //   row_k' =   -y * row_p +   x * row_k
                {
                    auto& row_p = m_U_inv[pivot_col];
                    auto& row_k = m_U_inv[k];
                    for (unsigned j = 0; j < n; ++j) {
                        mpq r_p = row_p[j];
                        mpq r_k = row_k[j];
                        mpq new_p = a_over_d * r_p + b_over_d * r_k;
                        mpq new_k = -y * r_p + x * r_k;
                        if (too_big(new_p) || too_big(new_k))
                            return false;
                        row_p[j] = new_p;
                        row_k[j] = new_k;
                    }
                }
            }

            // Force the pivot positive.
            if (m_H[r][pivot_col].is_neg()) {
                for (unsigned i = 0; i < m; ++i)
                    m_H[i][pivot_col] = -m_H[i][pivot_col];
                for (unsigned i = 0; i < n; ++i)
                    m_U[i][pivot_col] = -m_U[i][pivot_col];
                for (unsigned j = 0; j < n; ++j)
                    m_U_inv[pivot_col][j] = -m_U_inv[pivot_col][j];
            }

            // Off-diagonal reduction: for k < pivot_col, reduce H[r][k]
            // into [0, H[r][pivot_col]) by subtracting an integer
            // multiple of col_pivot_col from col_k.
            const mpq pivot_val = m_H[r][pivot_col];
            for (unsigned k = 0; k < pivot_col; ++k) {
                if (m_H[r][k].is_zero())
                    continue;
                mpq q = floor(m_H[r][k] / pivot_val);
                if (q.is_zero())
                    continue;
                if (too_big(q))
                    return false;
                for (unsigned i = 0; i < m; ++i) {
                    mpq new_v = m_H[i][k] - q * m_H[i][pivot_col];
                    if (too_big(new_v))
                        return false;
                    m_H[i][k] = new_v;
                }
                for (unsigned i = 0; i < n; ++i) {
                    mpq new_v = m_U[i][k] - q * m_U[i][pivot_col];
                    if (too_big(new_v))
                        return false;
                    m_U[i][k] = new_v;
                }
                // Column op col_k -= q col_p; inverse adds q row_k to row_p.
                auto& row_p = m_U_inv[pivot_col];
                auto& row_k = m_U_inv[k];
                for (unsigned j = 0; j < n; ++j) {
                    mpq new_v = row_p[j] + q * row_k[j];
                    if (too_big(new_v))
                        return false;
                    row_p[j] = new_v;
                }
            }
            pivot_col++;
        }
        return true;
    }

    void int_cube_hnf::compute_deltas() {
        unsigned m = m_H.size();
        unsigned n = m_U.size();
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
                // Row of H has a single +1 entry: term value = ±y_p, an
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
                s += abs(m_U[i][k]);
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

    bool int_cube_hnf::tighten_terms_for_hnf_cube() {
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

    bool int_cube_hnf::tighten_column_bound_by_delta(unsigned j, const impq& delta) {
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

    bool int_cube_hnf::tighten_columns_for_hnf_cube() {
        for (unsigned i = 0; i < m_J.size(); ++i) {
            if (!tighten_column_bound_by_delta(m_J[i], m_col_delta[i]))
                return false;
        }
        return true;
    }

    void int_cube_hnf::save_x_J() {
        unsigned n = m_J.size();
        m_saved_x_J.reset();
        m_saved_x_J.resize(n);
        for (unsigned i = 0; i < n; ++i)
            m_saved_x_J[i] = lra.get_column_value(m_J[i]);
    }

    void int_cube_hnf::apply_rounding() {
        unsigned n = m_J.size();
        // Compute y* = U_inv * x_J* in impq (preserve infinitesimal y component).
        vector<impq> y(n, impq(0));
        for (unsigned i = 0; i < n; ++i) {
            impq s(0);
            for (unsigned k = 0; k < n; ++k)
                s += m_saved_x_J[k] * m_U_inv[i][k];
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
        // z = U * y_round (now y has zero y-component since it's integer).
        vector<mpq> z(n, mpq(0));
        for (unsigned i = 0; i < n; ++i) {
            mpq s(0);
            for (unsigned k = 0; k < n; ++k)
                s += m_U[i][k] * y[k].x;
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

    lia_move int_cube_hnf::operator()() {
        lia.settings().stats().m_hnf_cube_calls++;
        TRACE(hnf_cube,
              for (unsigned j = 0; j < lra.number_of_vars(); ++j)
                  lia.display_column(tout, j);
              tout << lra.constraints();
            );

        if (!collect_J_and_terms()) {
            lia.settings().stats().m_hnf_cube_bail_collect++;
            return lia_move::undef;
        }
        if (!build_matrix()) {
            lia.settings().stats().m_hnf_cube_bail_build++;
            return lia_move::undef;
        }
        if (!compute_hnf()) {
            lia.settings().stats().m_hnf_cube_bail_hnf++;
            return lia_move::undef;
        }
        compute_deltas();

        lra.push();
        if (!tighten_terms_for_hnf_cube()) {
            lia.settings().stats().m_hnf_cube_bail_tighten++;
            lra.pop();
            lra.set_status(lp_status::OPTIMAL);
            return lia_move::undef;
        }
        if (!tighten_columns_for_hnf_cube()) {
            lia.settings().stats().m_hnf_cube_bail_tighten++;
            lra.pop();
            lra.set_status(lp_status::OPTIMAL);
            return lia_move::undef;
        }

        lp_status st = lra.find_feasible_solution();
        if (st != lp_status::FEASIBLE && st != lp_status::OPTIMAL) {
            lia.settings().stats().m_hnf_cube_bail_infeasible++;
            TRACE(hnf_cube, tout << "cannot find a feasible solution\n";);
            lra.pop();
            lra.move_non_basic_columns_to_bounds();
            return !lra.r_basis_has_inf_int() ? lia_move::sat : lia_move::undef;
        }
        save_x_J();
        lra.pop();
        apply_rounding();
        lra.set_status(lp_status::FEASIBLE);
        SASSERT(lia.settings().get_cancel_flag() || lia.is_feasible());
        TRACE(hnf_cube, tout << "hnf_cube success\n";);
        lia.settings().stats().m_hnf_cube_success++;
        return lia_move::sat;
    }
}
