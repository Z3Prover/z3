/**++
Copyright (c) 2020 Arie Gurfinkel

Module Name:

    spacer_arith_kernel.cpp

Abstract:

    Compute kernel of a matrix

Author:

    Hari Govind
    Arie Gurfinkel

Notes:

--*/

#include "muz/spacer/spacer_arith_kernel.h"

#include "math/simplex/sparse_matrix_def.h"
#include "math/simplex/sparse_matrix_ops.h"

using namespace spacer;

bool spacer_arith_kernel::compute_kernel() {
    SASSERT(m_matrix.num_rows() > 1);

    if (false && m_matrix.compute_linear_deps(m_kernel)) {
        // the matrix cannot be reduced further
        if (m_matrix.num_cols() - m_kernel.num_rows() <= 1) return true;

        m_kernel.reset(m_kernel.num_cols());
        SASSERT(m_matrix.num_cols() > 2);
    }
    if (m_matrix.num_cols() > 2) m_st.m_failed++;
    if (m_plugin /* && m_matrix.num_cols() > 2 */) {
        return m_plugin->compute_kernel(m_matrix, m_kernel, m_basic_vars);
    }
    return false;
}

namespace {
class simplex_arith_kernel_plugin : public spacer_arith_kernel::plugin {
  public:
    bool compute_kernel(const spacer_matrix &in, spacer_matrix &out,
                        vector<unsigned> &basics) override {
        using qmatrix = simplex::sparse_matrix<simplex::mpq_ext>;
        unsynch_mpq_manager m;
        qmatrix qmat(m);

        // extra column for column of 1
        qmat.ensure_var(in.num_cols());

        for (unsigned i = 0, n_rows = in.num_rows(); i < n_rows; ++i) {
            auto row_id = qmat.mk_row();
            unsigned j, n_cols;
            for (j = 0, n_cols = in.num_cols(); j < n_cols; ++j) {
                qmat.add_var(row_id, in.get(i, j).to_mpq(), j);
            }
            qmat.add_var(row_id, rational::one().to_mpq(), n_cols);
        }
        TRACE("gg", qmat.display(tout););

        qmatrix kern(m);
        simplex::sparse_matrix_ops::kernel_ffe<simplex::mpq_ext>(qmat, kern,
                                                                 basics);

        out.reset(kern.num_vars());
        vector<rational> vec;
        for (auto row : kern.get_rows()) {
            vec.reset();
            vec.reserve(kern.num_vars(), rational(0));
            for (auto &[coeff, v] : kern.get_row(row)) {
                vec[v] = rational(coeff);
            }
            out.add_row(vec);
        }

        TRACE("gg", {
            tout << "Computed kernel\n";
            qmat.display(tout);
            tout << "\n";
            kern.display(tout);
            tout << "\n";
            tout << "basics: " << basics << "\n";
            out.display(tout);
        });
        return out.num_rows() > 0;
    }

    void collect_statistics(statistics &st) const override {}
    void reset_statistics() override {}
    void reset() override {}
};

} // namespace

namespace spacer {

spacer_arith_kernel::plugin *mk_simplex_kernel_plugin() {
    return alloc(simplex_arith_kernel_plugin);
}
} // namespace spacer
