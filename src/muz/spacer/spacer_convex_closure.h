#pragma once
/**++
Copyright (c) 2020 Arie Gurfinkel

Module Name:

    spacer_convex_closure.h

Abstract:

   Compute convex closure of polyhedra

Author:

    Hari Govind
    Arie Gurfinkel

Notes:

--*/

#include "ast/arith_decl_plugin.h"
#include "ast/ast.h"
#include "ast/ast_util.h"
#include "muz/spacer/spacer_arith_kernel.h"
#include "muz/spacer/spacer_matrix.h"
#include "muz/spacer/spacer_util.h"
#include "util/statistics.h"

namespace spacer {

/// Computes a convex closure of a set of points
class convex_closure {
    struct stats {
        unsigned m_num_reductions;
        unsigned m_max_dim;
        stopwatch watch;
        stats() { reset(); }
        void reset() {
            m_num_reductions = 0;
            m_max_dim = 0;
            watch.reset();
        }
    };
    stats m_st;

    ast_manager &m;
    arith_util m_arith;
    bv_util m_bv;

    // size of all bit vectors in m_col_vars
    unsigned m_bv_sz;

    // Enable computation of implicit syntactic convex closure
    bool m_enable_implicit;

    // number of columns in \p m_data
    unsigned m_dim;

    // A vector of rational valued points
    spacer_matrix m_data;

    // Variables naming columns in `m_data`
    // \p m_col_vars[k] is a var for column \p k
    expr_ref_vector m_col_vars;
    vector<bool> m_dead_cols;

    // Kernel of \p m_data
    // Set at the end of computation
    spacer_arith_kernel m_kernel;

    // Free variables introduced by syntactic convex closure
    // These variables are always of sort Real
    expr_ref_vector m_alphas;

    expr_ref_vector m_implicit_cc;
    expr_ref_vector m_explicit_cc;

    /// Reduces dimension of \p m_data and returns its rank
    unsigned reduce();

    /// Constructs an equality corresponding to a given row in the kernel
    ///
    /// The equality is conceptually corresponds to
    ///    row * m_col_vars = 0
    /// where row is a row vector and m_col_vars is a column vector.
    /// However, the equality is put in a form so that exactly one variable from
    /// \p m_col_vars is on the LHS
    void kernel_row2eq(const vector<rational> &row, expr_ref &out);

    /// Construct all linear equations implied by points in \p m_data
    /// This is defined by \p m_kernel * m_col_vars = 0
    void kernel2fmls(expr_ref_vector &out);

    /// Compute syntactic convex closure of \p m_data
    void cc2fmls(expr_ref_vector &out);

    /// Construct the equality ((m_alphas . m_data[*][k]) = m_col_vars[k])
    ///
    /// \p m_data[*][k] is the kth column of m_data
    /// The equality is added to \p out.
    void cc_col2eq(unsigned k, expr_ref_vector &out);

    /// Compute one dimensional convex closure over \p var
    ///
    /// \p var is the dimension over  which convex closure is computed
    /// Result is stored in \p out
    void cc_1dim(const expr_ref &var, expr_ref_vector &out);

    /// Computes div constraint implied by a set of data points
    ///
    /// Finds the largest numbers \p m, \p d such that \p m_data[i] mod m = d
    /// Returns true if successful
    bool infer_div_pred(const vector<rational> &data, rational &m, rational &d);

    /// Constructs a formula \p var ~ n , where  ~ = is_le ? <= : >=
    expr *mk_le_ge(expr *var, rational n, bool is_le);

    expr *mk_add(const expr_ref_buffer &vec);
    expr *mk_numeral(const rational &n, bool is_int);

    /// Returns equality (v = r mod d)
    expr *mk_eq_mod(expr *v, rational d, rational r);

    bool has_bv() { return m_bv_sz > 0; }

  public:
    convex_closure(ast_manager &_m);

    /// Resets all data points
    ///
    /// n_cols is the number of dimensions of new expected data points
    void reset(unsigned n_cols);

    /// Turn support for fixed sized bit-vectors of size \p sz
    ///
    /// Disables syntactic convex closure as a side-effect
    void set_bv(unsigned sz) {
        SASSERT(sz > 0);
        m_bv_sz = sz;
        m_enable_implicit = false;
    }

    /// \brief Name dimension \p i with a variable \p v.
    void set_col_var(unsigned i, expr *v) {
        SASSERT(i < dims());
        SASSERT(m_col_vars.get(i) == nullptr);
        m_col_vars[i] = v;
    }

    /// \brief Return number of dimensions of each point
    unsigned dims() const { return m_dim; }

    /// \brief Add an n-dimensional point to convex closure
    void add_row(const vector<rational> &point) {
        SASSERT(point.size() == dims());
        m_data.add_row(point);
    };

    bool operator()() { return this->compute(); }
    bool compute();
    bool has_implicit() { return !m_implicit_cc.empty(); }
    bool has_explicit() { return !m_explicit_cc.empty(); }

    /// Returns the implicit component of convex closure (if available)
    ///
    /// Implicit component contains constants from get_alphas() that are
    /// implicitly existentially quantified
    const expr_ref_vector &get_implicit() { return m_implicit_cc; }

    /// \brief Return implicit constants in implicit convex closure
    const expr_ref_vector &get_alphas() const { return m_alphas; }

    /// Returns the explicit component of convex closure (if available)
    ///
    /// The explicit component is in term of column variables
    const expr_ref_vector &get_explicit() { return m_explicit_cc; }

    /// Returns constants used to name columns
    ///
    /// Explicit convex closure is in terms of these variables
    const expr_ref_vector &get_col_vars() { return m_col_vars; }

    void collect_statistics(statistics &st) const;
    void reset_statistics() { m_st.reset(); }
};
} // namespace spacer
