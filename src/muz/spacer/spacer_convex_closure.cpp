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
#include "ast/rewriter/th_rewriter.h"

namespace {

#ifdef Z3DEBUG
bool is_int_matrix(const spacer::spacer_matrix &matrix) {
    for (unsigned i = 0, rows = matrix.num_rows(); i < rows; i++) 
        for (unsigned j = 0, cols = matrix.num_cols(); j < cols; j++)
            if (!matrix.get(i, j).is_int()) 
                return false;
    return true;
}

bool is_sorted(const vector<rational> &data) {
    for (unsigned i = 0; i < data.size() - 1; i++) 
        if (!(data[i] >= data[i + 1])) 
            return false;
    return true;
}
#endif

/// Check whether all elements of \p data are congruent modulo \p m
bool is_congruent_mod(const vector<rational> &data, const rational &m) {
    SASSERT(data.size() > 0);
    rational p = data[0] % m;
    for (auto k : data)
        if (k % m != p) return false;
    return true;
}

app *mk_bvadd(bv_util &bv, unsigned num, expr *const *args) {
    if (num == 0) return nullptr;
    if (num == 1) return is_app(args[0]) ? to_app(args[0]) : nullptr;

    if (num == 2) { return bv.mk_bv_add(args[0], args[1]); }

    /// XXX no mk_bv_add for n-ary bv_add
    return bv.get_manager().mk_app(bv.get_fid(), OP_BADD, num, args);
}
} // namespace

namespace spacer {

convex_closure::convex_closure(ast_manager &_m)
    : m(_m), m_arith(m), m_bv(m), m_bv_sz(0), m_enable_implicit(true), m_dim(0),
      m_data(0, 0), m_col_vars(m), m_kernel(m_data), m_alphas(m),
      m_implicit_cc(m), m_explicit_cc(m) {

    m_kernel.set_plugin(mk_simplex_kernel_plugin());
}
void convex_closure::reset(unsigned n_cols) {
    m_dim = n_cols;
    m_kernel.reset();
    m_data.reset(m_dim);
    m_col_vars.reset();
    m_col_vars.reserve(m_dim);
    m_dead_cols.reset();
    m_dead_cols.reserve(m_dim, false);
    m_alphas.reset();
    m_bv_sz = 0;
    m_enable_implicit = true;
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
unsigned convex_closure::reduce() {
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

    for (auto v : m_kernel.get_basic_vars())
        // XXX sometimes a constant can be basic, need to find a way to
        // switch it to var
        if (v < m_dead_cols.size()) m_dead_cols[v] = true;
    return m_dim - ker.num_rows();
}

// For row \p row in m_kernel, construct the equality:
//
// row * m_col_vars = 0
//
// In the equality, exactly one variable from  m_col_vars is on the lhs
void convex_closure::kernel_row2eq(const vector<rational> &row, expr_ref &out) {
    expr_ref_buffer lhs(m);
    expr_ref e1(m);

    bool is_int = false;
    for (unsigned i = 0, sz = row.size(); i < sz; ++i) {
        rational val_i = row.get(i);
        if (val_i.is_zero()) continue;
        SASSERT(val_i.is_int());

        if (i < sz - 1) {
            e1 = m_col_vars.get(i);
            is_int |= m_arith.is_int(e1);
            mul_by_rat(e1, val_i);
        } else {
            e1 = mk_numeral(val_i, is_int);
        }
        lhs.push_back(e1);
    }

    e1 = !has_bv() ? mk_add(lhs) : mk_bvadd(m_bv, lhs.size(), lhs.data());
    e1 = m.mk_eq(e1, mk_numeral(rational::zero(), is_int));

    // revisit this simplification step, it is here only to prevent/simplify
    // formula construction everywhere else
    params_ref params;
    params.set_bool("som", true);
    params.set_bool("flat", true);
    th_rewriter rw(m, params);
    rw(e1, out);
}

/// Generates linear equalities implied by m_data
///
/// the linear equalities are m_kernel * m_col_vars = 0 (where * is matrix
/// multiplication) the new equalities are stored in m_col_vars for each row
/// [0, 1, 0, 1 , 1] in m_kernel, the equality v1 = -1*v3 + -1*1 is
/// constructed and stored at index 1 of m_col_vars
void convex_closure::kernel2fmls(expr_ref_vector &out) {
    // assume kernel has been computed already
    const spacer_matrix &kern = m_kernel.get_kernel();
    SASSERT(kern.num_rows() > 0);

    TRACE("cvx_dbg", kern.display(tout););
    expr_ref eq(m);
    for (unsigned i = kern.num_rows(); i > 0; i--) {
        auto &row = kern.get_row(i - 1);
        kernel_row2eq(row, eq);
        out.push_back(eq);
    }
}

expr *convex_closure::mk_add(const expr_ref_buffer &vec) {
    SASSERT(!vec.empty());
    expr_ref s(m);
    if (vec.size() == 1) {
        return vec[0];
    } else if (vec.size() > 1) {
        return m_arith.mk_add(vec.size(), vec.data());
    }

    UNREACHABLE();
    return nullptr;
}

expr *convex_closure::mk_numeral(const rational &n, bool is_int) {
    if (!has_bv())
        return m_arith.mk_numeral(n, is_int);
    else
        return m_bv.mk_numeral(n, m_bv_sz);
}

/// Construct the equality ((m_alphas . m_data[*][i]) = m_col_vars[i])
///
/// Where . is the dot product,  m_data[*][i] is
/// the ith column of m_data. Add the result to res_vec.
void convex_closure::cc_col2eq(unsigned col, expr_ref_vector &out) {
    SASSERT(!has_bv());

    expr_ref_buffer sum(m);
    for (unsigned row = 0, sz = m_data.num_rows(); row < sz; row++) {
        expr_ref alpha(m);
        auto n = m_data.get(row, col);
        if (n.is_zero()) {
            ; // noop
        } else {
            alpha = m_alphas.get(row);
            if (!n.is_one()) {
                alpha = m_arith.mk_mul(
                    m_arith.mk_numeral(n, false /* is_int */), alpha);
            }
        }
        if (alpha) sum.push_back(alpha);
    }
    SASSERT(!sum.empty());
    expr_ref s(m);
    s = mk_add(sum);

    expr_ref v(m);
    expr *vi = m_col_vars.get(col);
    v = m_arith.is_int(vi) ? m_arith.mk_to_real(vi) : vi;
    out.push_back(m.mk_eq(s, v));
}

void convex_closure::cc2fmls(expr_ref_vector &out) {
    sort_ref real_sort(m_arith.mk_real(), m);
    expr_ref zero(m_arith.mk_real(rational::zero()), m);

    for (unsigned row = 0, sz = m_data.num_rows(); row < sz; row++) {
        if (row >= m_alphas.size()) {
            m_alphas.push_back(m.mk_fresh_const("a!cc", real_sort));
        }
        SASSERT(row < m_alphas.size());
        // forall j :: alpha_j >= 0
        out.push_back(m_arith.mk_ge(m_alphas.get(row), zero));
    }

    for (unsigned k = 0, sz = m_col_vars.size(); k < sz; k++) {
        if (m_col_vars.get(k) && !m_dead_cols[k]) cc_col2eq(k, out);
    }

    //(\Sum j . m_new_vars[j]) = 1
    out.push_back(m.mk_eq(
        m_arith.mk_add(m_data.num_rows(),
                       reinterpret_cast<expr *const *>(m_alphas.data())),
        m_arith.mk_real(rational::one())));
}

#define MAX_DIV_BOUND 101
// check whether \exists m, d s.t data[i] mod m = d. Returns the largest m and
// corresponding d
// TODO: find the largest divisor, not the smallest.
// TODO: improve efficiency
bool convex_closure::infer_div_pred(const vector<rational> &data, rational &m,
                                    rational &d) {
    TRACE("cvx_dbg_verb", {
        tout << "computing div constraints for ";
        for (rational r : data) tout << r << " ";
        tout << "\n";
    });
    SASSERT(data.size() > 1);
    SASSERT(is_sorted(data));

    m = rational(2);

    // special handling for even/odd
    if (is_congruent_mod(data, m)) {
      mod(data.back(), m, d);
      return true;
    }

    // hard cut off to save time
    rational bnd(MAX_DIV_BOUND);
    rational big = data.back();
    // AG: why (m < big)?  Note that 'big' is the smallest element of data
    for (; m < big && m < bnd; m++) {
        if (is_congruent_mod(data, m)) break;
    }
    if (m >= big) return false;
    if (m == bnd) return false;

    mod(data[0], m, d);
    SASSERT(d >= rational::zero());

    TRACE("cvx_dbg_verb", tout << "div constraint generated. cf " << m
                               << " and off " << d << "\n";);
    return true;
}

bool convex_closure::compute() {
    scoped_watch _w_(m_st.watch);
    SASSERT(is_int_matrix(m_data));

    unsigned rank = reduce();
    // store dim var before rewrite
    expr_ref var(m_col_vars.get(0), m);
    if (rank < dims()) {
        m_st.m_num_reductions++;
        kernel2fmls(m_explicit_cc);
        TRACE("cvx_dbg", tout << "Linear equalities true of the matrix "
                              << mk_and(m_explicit_cc) << "\n";);
    }

    m_st.m_max_dim = std::max(m_st.m_max_dim, rank);

    if (rank == 0) {
        // AG: Is this possible?
        return false;
    } else if (rank > 1) {
        if (m_enable_implicit) {
            TRACE("subsume", tout << "Computing syntactic convex closure\n";);
            cc2fmls(m_implicit_cc);
        } else {
            return false;
        }
        return true;
    }

    SASSERT(rank == 1);
    cc_1dim(var, m_explicit_cc);
    return true;
}

// construct the formula result_var <= bnd or result_var >= bnd
expr *convex_closure::mk_le_ge(expr *v, rational n, bool is_le) {
    if (m_arith.is_int_real(v)) {
        expr *en = m_arith.mk_numeral(n, m_arith.is_int(v));
        return is_le ? m_arith.mk_le(v, en) : m_arith.mk_ge(v, en);
    } else if (m_bv.is_bv(v)) {
        expr *en = m_bv.mk_numeral(n, m_bv.get_bv_size(v->get_sort()));
        return is_le ? m_bv.mk_ule(v, en) : m_bv.mk_ule(en, v);
    } else {
        UNREACHABLE();
    }

    return nullptr;
}

void convex_closure::cc_1dim(const expr_ref &var, expr_ref_vector &out) {

    // XXX assumes that var corresponds to col 0

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
    // upper-bound
    out.push_back(mk_le_ge(res, data[0], true));
    // lower-bound
    out.push_back(mk_le_ge(res, data.back(), false));

    // -- compute divisibility constraints
    rational cr, off;
    // add div constraints for all variables.
    for (unsigned j = 0; j < m_data.num_cols(); j++) {
        auto *v = m_col_vars.get(j);
        if (v && (m_arith.is_int(v) || m_bv.is_bv(v))) {
            data.reset();
            m_data.get_col(j, data);
            std::sort(data.begin(), data.end(), gt_proc);
            if (infer_div_pred(data, cr, off)) {
                out.push_back(mk_eq_mod(v, cr, off));
            }
        }
    }
}

expr *convex_closure::mk_eq_mod(expr *v, rational d, rational r) {
    expr *res = nullptr;
    if (m_arith.is_int(v)) {
        res = m.mk_eq(m_arith.mk_mod(v, m_arith.mk_int(d)), m_arith.mk_int(r));
    } else if (m_bv.is_bv(v)) {
        res = m.mk_eq(m_bv.mk_bv_urem(v, m_bv.mk_numeral(d, m_bv_sz)),
                      m_bv.mk_numeral(r, m_bv_sz));
    } else {
        UNREACHABLE();
    }
    return res;
}

} // namespace spacer
