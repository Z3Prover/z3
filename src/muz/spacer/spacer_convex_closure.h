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

    // size of all bit vectors in m_dim_vars
    unsigned m_bv_sz;

    // Compute syntactic convex closure
    bool m_enable_syntactic_cc;

    // true if \p m_dim_vars are arithmetic sort (i.e., Real or Int)
    bool m_is_arith;

    // size of \p m_dim_vars
    unsigned m_dim;

    // A vector of rational valued points
    spacer_matrix m_data;

    // Variables naming dimensions in `m_data`
    // \p m_dim_vars[i] is variable naming dimension \p i
    var_ref_vector m_dim_vars;

    // Kernel of \p m_data
    // Set at the end of computation
    spacer_arith_kernel m_kernel;

    // Free variables introduced by syntactic convex closure
    // These variables are always of sort Real
    var_ref_vector m_new_vars;

    // m_lcm is a hack to allow convex_closure computation of rational matrices
    // as well. Let A be a real matrix. m_lcm is the lcm of all denominators in
    // A m_data = m_lcm * A, is always an integer matrix
    // TODO: m_lcm should be maintained by the client
    rational m_lcm;

    /// Reduces dimension of \p m_data and returns its rank
    unsigned reduce_dim();

    /// Constructs an equality corresponding to a given row in the kernel
    ///
    /// The equality is conceptually corresponds to
    ///    row * m_dim_vars = 0
    /// where row is a row vector and m_dim_vars is a column vector.
    /// However, the equality is put in a form so that exactly one variable from
    /// \p m_dim_vars is on the LHS
    void generate_equality_for_row(const vector<rational> &row, expr_ref &out);

    /// Construct all linear equations implied by points in \p m_data
    /// This is defined by \p m_kernel * m_dim_vars = 0
    void generate_implied_equalities(expr_ref_vector &out);

    /// Compute syntactic convex closure of \p m_data
    void syntactic_convex_closure(expr_ref_vector &out);

    /// Construct the equality ((m_nw_vars . m_data[*][j]) = m_dim_vars[j])
    ///
    /// \p m_data[*][j] is the jth column of m_data
    /// The equality is added to \p out.
    void add_sum_cnstr(unsigned j, expr_ref_vector &out);

    /// Compute one dimensional convex closure over \p var
    ///
    /// \p var is the dimension over  which convex closure is computed
    /// Result is stored in \p out
    void do_1dim_convex_closure(const expr_ref &var, expr_ref_vector &out);

    /// Computes div constraint implied by a set of data points
    ///
    /// Finds the largest numbers \p m, \p d such that \p m_data[i] mod m = d
    /// Returns true if successful
    bool compute_div_constraint(const vector<rational> &data, rational &m,
                                rational &d);

    /// Constructs a formula \p var ~ bnd, where  ~ = is_le ? <= : >=
    expr *mk_ineq(expr_ref var, rational bnd, bool is_le);

  public:
    convex_closure(ast_manager &manager, bool use_sage)
        : m(manager), m_arith(m), m_bv(m), m_bv_sz(0), m_enable_syntactic_cc(true),
          m_is_arith(true), m_dim(0), m_data(0, 0), m_dim_vars(m),
          m_kernel(m_data), m_new_vars(m) {

        if (use_sage) m_kernel.set_plugin(mk_sage_plugin());
    }

    /// Resets all data points
    ///
    /// n_cols is the number of dimensions of new expected data points
    void reset(unsigned n_cols);

    /// Turn support for fixed sized bit-vectors of size \p sz
    ///
    /// Disables syntactic convex closure as a side-effect
    void set_bv(unsigned sz) {
        SASSERT(sz > 0);
        m_is_arith = false;
        m_bv_sz = sz;
        m_enable_syntactic_cc = false;
    }

    /// \brief Name dimension \p i with a variable \p v.
    void set_dimension(unsigned i, var *v) {
        SASSERT(i < dims());
        SASSERT(m_dim_vars[i] == nullptr);
        m_dim_vars[i] = v;
    }

    /// \brief Return number of dimensions of each point
    unsigned dims() const { return m_dim; }

    /// \brief Return variables introduced by the syntactic convex closure
    const var_ref_vector &get_new_vars() const { return m_new_vars; }

    /// \brief Add a one-dimensional point to convex closure
    void push_back(rational x) {
        SASSERT(dims() == 1);
        vector<rational> row;
        row.reserve(1, x);
        m_data.add_row(row);
    }

    /// \brief Add a two-dimensional point to convex closure
    void push_back(rational x, rational y) {
        SASSERT(dims() == 2);
        vector<rational> row;
        row.reserve(2);
        row[0] = x;
        row[1] = y;
        m_data.add_row(row);
    }

    /// \brief Add an n-dimensional point to convex closure
    void push_back(const vector<rational> &point) {
        SASSERT(point.size() == dims());
        m_data.add_row(point);
    };

    /// \brief Compute convex closure of the current set of points
    ///
    /// Returns true if successful and \p out is an exact convex closure
    /// Returns false if \p out is an over-approximation
    bool closure(expr_ref_vector &out);

    void collect_statistics(statistics &st) const;
    void reset_statistics() { m_st.reset(); }

    /// Set the least common multiple of \p m_data
    void set_lcm(rational l) { m_lcm = l; }
};
} // namespace spacer
