/**++
Copyright (c) 2020 Arie Gurfinkel

Module Name:

    spacer_convex_closure.cpp

Abstract:

   Compute convex closure of polyhedra

Author:

    Hari Govind
    Arie Gurfinkel

Notes:

--*/

#include "muz/spacer/spacer_convex_closure.h"

namespace {
bool is_int_matrix(const spacer::spacer_matrix &matrix) {
    rational val;
    for (unsigned i = 0, rows = matrix.num_rows(); i < rows; i++) {
        for (unsigned j = 0, cols = matrix.num_cols(); j < cols; j++)
            if (!matrix.get(i, j).is_int()) return false;
    }
    return true;
}

bool is_sorted(const vector<rational> &data) {
    for (unsigned i = 0; i < data.size() - 1; i++) {
        if (!(data[i] >= data[i + 1])) return false;
    }
    return true;
}

/// Check whether all elements of \p data are congruent modulo \p m
bool is_congruent_mod(const vector<rational> &data, rational m) {
    SASSERT(data.size() > 0);
    rational p = data[0] % m;
    for (auto k : data)
        if (k % m != p) return false;
    return true;
}

app *mk_bvadd(ast_manager &m, unsigned num, expr *const *args) {
    if (num == 0) return nullptr;
    if (num == 1) return is_app(args[0]) ? to_app(args[0]) : nullptr;

    bv_util bv(m);
    if (num == 2) { return bv.mk_bv_add(args[0], args[1]); }

    /// XXX no mk_bv_add for n-ary bv_add
    return m.mk_app(bv.get_fid(), OP_BADD, num, args);
}
} // namespace

namespace spacer {

void convex_closure::reset(unsigned n_cols) {
    m_kernel.reset();
    m_data.reset(n_cols);
    m_dim_vars.reset();
    m_dim = n_cols;
    m_dim_vars.reserve(m_dim);
    m_new_vars.reset();
    m_bv_sz = 0;
    m_enable_syntactic_cc = true;
}

void convex_closure::collect_statistics(statistics &st) const {
    st.update("time.spacer.solve.reach.gen.global.cc",
              m_st.watch.get_seconds());
    st.update("SPACER cc num dim reduction success", m_st.m_num_reductions);
    st.update("SPACER cc max reduced dim", m_st.m_max_dim);
    m_kernel.collect_statistics(st);
}

// call m_kernel to reduce dimensions of m_data
// return the rank of m_data
unsigned convex_closure::reduce_dim() {
    if (m_dim <= 1) return m_dim;

    bool has_kernel = m_kernel.compute_kernel();
    if (!has_kernel) {
        TRACE("cvx_dbg",
              tout << "No linear dependencies between pattern vars\n";);
        return m_dim;
    }

    const spacer_matrix &ker = m_kernel.get_kernel();
    SASSERT(ker.num_rows() > 0);
    SASSERT(ker.num_rows() <= m_dim);
    SASSERT(ker.num_cols() == m_dim + 1);
    // m_dim - ker.num_rows() is the number of variables that have no linear
    // dependencies
    return m_dim - ker.num_rows();
}

// For row \p row in m_kernel, construct the equality:
//
// row * m_dim_vars = 0
//
// In the equality, exactly one variable from  m_dim_vars is on the lhs
void convex_closure::generate_equality_for_row(const vector<rational> &row,
                                               expr_ref &out) {
    // contains the right hand side of an equality
    expr_ref_buffer rhs(m);
    // index of first non zero element in row
    int pv = -1;
    // are we constructing rhs or lhs
    bool is_lhs = true;
    // coefficient of m_dim_vars[pv]
    rational coeff(1);

    // the elements in row are the coefficients of m_dim_vars
    // some elements should go to the rhs, in which case the signs are
    // changed
    for (unsigned j = 0, sz = row.size(); j < sz; j++) {
        rational val = row.get(j);
        SASSERT(val.is_int());
        if (val.is_zero()) continue;
        if (is_lhs) {
            // Cannot re-write the last element
            if (j == row.size() - 1) continue;
            SASSERT(pv == -1);
            pv = j;
            is_lhs = false;
            // In integer echelon form, the pivot need not be 1
            coeff = val;
        } else {
            expr_ref prod(m);
            if (j != row.size() - 1) {
                prod = m_dim_vars.get(j);
                mul_by_rat(prod, -1 * val * m_lcm);
            } else {
                if (m_arith.is_int(m_dim_vars.get(pv))) {
                    prod = m_arith.mk_int(-1 * val);
                } else if (m_arith.is_real(m_dim_vars.get(pv))) {
                    prod = m_arith.mk_real(-1 * val);
                } else if (m_bv.is_bv(m_dim_vars.get(pv))) {
                    prod = m_bv.mk_numeral(-1 * val, m_bv_sz);
                }
            }
            SASSERT(prod.get());
            rhs.push_back(prod);
        }
    }

    // make sure that there is a non-zero entry
    SASSERT(pv != -1);

    if (rhs.size() == 0) {
        expr_ref _rhs(m);
        if (m_arith.is_int(m_dim_vars.get(pv)))
            _rhs = m_arith.mk_int(rational::zero());
        else if (m_arith.is_real(m_dim_vars.get(pv)))
            _rhs = m_arith.mk_real(rational::zero());
        else if (m_bv.is_bv(m_dim_vars.get(pv)))
            _rhs = m_bv.mk_numeral(rational::zero(), m_bv_sz);
        out = m_arith.mk_eq(m_dim_vars.get(pv), _rhs);
        return;
    }

    out = m_is_arith ? m_arith.mk_add(rhs.size(), rhs.data())
                     : mk_bvadd(m, rhs.size(), rhs.data());
    expr_ref pv_var(m);
    pv_var = m_dim_vars.get(pv);
    mul_by_rat(pv_var, coeff * m_lcm);

    out = m.mk_eq(pv_var, out);
    TRACE("cvx_dbg", tout << "rewrote " << mk_pp(m_dim_vars.get(pv), m)
                          << " into " << out << "\n";);
}

/// Generates linear equalities implied by m_data
///
/// the linear equalities are m_kernel * m_dim_vars = 0 (where * is matrix
/// multiplication) the new equalities are stored in m_dim_vars for each row [0,
/// 1, 0, 1 , 1] in m_kernel, the equality m_lcm*v1 = -1*m_lcm*v3 + -1*1 is
/// constructed and stored at index 1 of m_dim_vars
void convex_closure::generate_implied_equalities(expr_ref_vector &out) {
    // assume kernel has been computed already
    const spacer_matrix &kern = m_kernel.get_kernel();
    SASSERT(kern.num_rows() > 0);

    expr_ref eq(m);
    for (unsigned i = kern.num_rows(); i > 0; i--) {
        auto &row = kern.get_row(i - 1);
        generate_equality_for_row(row, eq);
        out.push_back(eq);
    }
}

/// Construct the equality ((m_new_vars . m_data[*][i]) = m_dim_vars[i])
///
/// Where . is the dot product,  m_data[*][i] is
/// the ith column of m_data. Add the result to res_vec.
void convex_closure::add_sum_cnstr(unsigned i, expr_ref_vector &out) {
    expr_ref_buffer sum(m);
    expr_ref prod(m), v(m);
    for (unsigned j = 0, sz = m_new_vars.size(); j < sz; j++) {
        prod = m_new_vars.get(j);
        mul_by_rat(prod, m_data.get(j, i));
        sum.push_back(prod);
    }
    v = m_arith.mk_to_real(m_dim_vars.get(i));
    mul_by_rat(v, m_lcm);
    if (m_is_arith)
        out.push_back(m.mk_eq(m_arith.mk_add(sum.size(), sum.data()), v));
    else
        out.push_back(m.mk_eq(mk_bvadd(m, sum.size(), sum.data()), v));
}

void convex_closure::syntactic_convex_closure(expr_ref_vector &out) {
    for (unsigned i = 0; i < m_data.num_rows(); i++) {
        var *v = m.mk_var(i + dims(), m_arith.mk_real());
        m_new_vars.push_back(v);
    }

    // forall j :: m_new_vars[j] >= 0
    for (auto v : m_new_vars) {
        out.push_back(m_arith.mk_ge(v, m_arith.mk_real(rational::zero())));
    }

    for (unsigned i = 0, sz = m_dim_vars.size(); i < sz; i++) {
        if (is_var(m_dim_vars.get(i))) add_sum_cnstr(i, out);
    }

    //(\Sum j . m_new_vars[j]) = 1
    out.push_back(m.mk_eq(
        m_arith.mk_add(m_new_vars.size(),
                       reinterpret_cast<expr *const *>(m_new_vars.data())),
        m_arith.mk_real(rational::one())));
}

#define MAX_DIV_BOUND 101
// check whether \exists m, d s.t data[i] mod m = d. Returns the largest m and
// corresponding d
// TODO: find the largest divisor, not the smallest.
// TODO: improve efficiency
bool convex_closure::compute_div_constraint(const vector<rational> &data,
                                            rational &m, rational &d) {
    TRACE("cvx_dbg_verb", {
        tout << "computing div constraints for ";
        for (rational r : data) tout << r << " ";
        tout << "\n";
    });
    SASSERT(data.size() > 1);
    SASSERT(is_sorted(data));

    m = rational(2);
    // hard cut off to save time
    rational bnd(MAX_DIV_BOUND);
    rational big = data.back();
    for (; m < big && m < bnd; m++) {
        if (is_congruent_mod(data, m)) break;
    }
    if (m >= big) return false;
    if (m == bnd) return false;

    d = data[0] % m;
    // work around for z3::rational::rem returning negative numbers.
    d = (m + d) % m;
    SASSERT(d >= rational::zero());

    TRACE("cvx_dbg_verb", tout << "div constraint generated. cf " << m
                               << " and off " << d << "\n";);
    return true;
}

/// Compute the convex closure of points in m_data
///
/// Returns true if the convex closure is syntactic
bool convex_closure::closure(expr_ref_vector &out) {
    scoped_watch _w_(m_st.watch);
    SASSERT(is_int_matrix(m_data));

    unsigned red_dim = reduce_dim();

    // store dim var before rewrite
    expr_ref var(m_dim_vars.get(0), m);
    if (red_dim < dims()) {
        m_st.m_num_reductions++;
        generate_implied_equalities(out);
        TRACE("cvx_dbg", tout << "Linear equalities true of the matrix "
                              << mk_and(out) << "\n";);
    }

    if (red_dim > m_st.m_max_dim) m_st.m_max_dim = red_dim;

    if (red_dim > 1) {
        // there is no alternative to syntactic convex closure right now
        // syntactic convex closure does not support BV
        if (m_enable_syntactic_cc) {
            SASSERT(m_new_vars.size() == 0);
            TRACE("subsume", tout << "Computing syntactic convex closure\n";);
            syntactic_convex_closure(out);
        } else {
            out.reset();
            return false;
        }
        return true;
    }

    // zero dimensional convex closure
    if (red_dim == 0) { return false; }

    SASSERT(red_dim == 1);
    do_1dim_convex_closure(var, out);
    return false;
}

// construct the formula result_var <= bnd or result_var >= bnd
expr *convex_closure::mk_ineq(expr_ref result_var, rational bnd, bool is_le) {
    if (m_is_arith) {
        // The resulting expr is of sort Real if result_var is of sort Real.
        // Otherwise, the resulting expr is of sort Int
        if (is_le) return m_arith.mk_le(result_var, m_arith.mk_int(bnd));
        return m_arith.mk_ge(result_var, m_arith.mk_int(bnd));
    }
    // TODO figure out whether we need signed versions or unsigned versions.
    if (is_le) return m_bv.mk_ule(result_var, m_bv.mk_numeral(bnd, m_bv_sz));
    return m_bv.mk_ule(m_bv.mk_numeral(bnd, m_bv_sz), result_var);
}

void convex_closure::do_1dim_convex_closure(const expr_ref &var,
                                            expr_ref_vector &out) {
    // The convex closure over one dimension is just a bound
    vector<rational> data;
    m_data.get_col(0, data);
    auto gt_proc = [](rational const &x, rational const &y) -> bool {
        return x > y;
    };
    std::sort(data.begin(), data.end(), gt_proc);

    // -- compute LB <= var <= UB
    expr_ref res(m);
    res = var;
    mul_by_rat(res, m_lcm);
    // upper-bound
    out.push_back(mk_ineq(res, data[0], true));
    // lower-bound
    out.push_back(mk_ineq(res, data.back(), false));

    // -- compute divisibility constraints
    rational cr, off;
    // add div constraints for all variables.
    for (unsigned j = 0; j < m_data.num_cols(); j++) {
        auto *v = m_dim_vars.get(j);
        if (is_var(v) && (m_arith.is_int(v) || m_bv.is_bv(v))) {
            data.reset();
            m_data.get_col(j, data);
            std::sort(data.begin(), data.end(), gt_proc);
            if (compute_div_constraint(data, cr, off)) {
                res = v;
                mul_by_rat(res, m_lcm);
                if (m_is_arith) {
                    res = m.mk_eq(m_arith.mk_mod(res, m_arith.mk_int(cr)),
                                  m_arith.mk_int(off));
                } else {
                    res = m.mk_eq(
                        m_bv.mk_bv_urem(res, m_bv.mk_numeral(cr, m_bv_sz)),
                        m_bv.mk_numeral(off, m_bv_sz));
                }
                out.push_back(res);
            }
        }
    }
}

} // namespace spacer
