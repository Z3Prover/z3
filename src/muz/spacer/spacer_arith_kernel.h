#pragma once
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

#include "spacer_matrix.h"
#include "util/statistics.h"
namespace spacer {

/**
   Computes a kernel of a matrix.
*/
class spacer_arith_kernel {
  public:
    class plugin {
      public:
        virtual ~plugin() {}
        virtual bool compute_kernel(const spacer_matrix &in_matrix,
                                    spacer_matrix &out_kernel,
                                    vector<unsigned> &basics) = 0;
        virtual void collect_statistics(statistics &st) const = 0;
        virtual void reset_statistics() = 0;
        virtual void reset() = 0;
    };

  protected:
    struct stats {
        unsigned m_failed;
        stats() { reset(); }
        void reset() { m_failed = 0; }
    };
    stats m_st;

    /// Input matrix for which kernel is to be computed
    const spacer_matrix &m_matrix;

    /// Output matrix representing the kernel
    spacer_matrix m_kernel;
    /// columns in the kernel that correspond to basic vars
    vector<unsigned> m_basic_vars;

    scoped_ptr<plugin> m_plugin;

  public:
    spacer_arith_kernel(spacer_matrix &matrix)
        : m_matrix(matrix), m_kernel(0, 0) {}
    virtual ~spacer_arith_kernel() = default;

    void set_plugin(spacer_arith_kernel::plugin *plugin) { m_plugin = plugin; }

    /// Computes kernel of a matrix
    /// returns true if the computation was successful
    /// use \p spacer_arith_kernel::get_kernel() to get the kernel
    bool compute_kernel();
    bool operator()() { return compute_kernel(); }

    const spacer_matrix &get_kernel() const { return m_kernel; }
    const vector<unsigned> &get_basic_vars() const { return m_basic_vars; }

    void reset() {
        m_kernel = spacer_matrix(0, 0);
        if (m_plugin) m_plugin->reset();
    }

    virtual void collect_statistics(statistics &st) const {
        st.update("SPACER arith kernel failed", m_st.m_failed);
        if (m_plugin) { m_plugin->collect_statistics(st); }
    }
    virtual void reset_statistics() {
        m_st.reset();
        if (m_plugin) m_plugin->reset_statistics();
    }
};

spacer_arith_kernel::plugin *mk_simplex_kernel_plugin();

} // namespace spacer
