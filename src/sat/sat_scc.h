/*++
Copyright (c) 2011 Microsoft Corporation

Module Name:

    sat_scc.h

Abstract:

    Use binary clauses to compute strongly connected components.

Author:

    Leonardo de Moura (leonardo) 2011-05-26.

Revision History:

--*/
#ifndef SAT_SCC_H_
#define SAT_SCC_H_

#include "sat/sat_types.h"
#include "util/statistics.h"
#include "util/params.h"

namespace sat {
    class solver;

    class scc {
        struct report;
        solver &   m_solver;
        // config
        bool       m_scc;
        bool       m_scc_tr;
        // stats
        unsigned   m_num_elim;
        unsigned   m_num_elim_bin;
        random_gen m_rand;

        // BIG state:

        vector<literal_vector> m_dag;
        svector<bool>          m_roots;
        svector<int>           m_left, m_right;
        literal_vector         m_root, m_parent;

        void reduce_tr();
        unsigned reduce_tr(bool learned);

        void init_dfs_num(bool learned);

        struct pframe;

    public:

        scc(solver & s, params_ref const & p);
        unsigned operator()();

        void updt_params(params_ref const & p);
        static void collect_param_descrs(param_descrs & d);

        void collect_statistics(statistics & st) const;
        void reset_statistics();

        /*
          \brief create binary implication graph and associated data-structures to check transitivity.
         */
        void init_big(bool learned);
        int get_left(literal l) const { return m_left[l.index()]; }
        int get_right(literal l) const { return m_right[l.index()]; }
        literal get_parent(literal l) const { return m_parent[l.index()]; }
        literal get_root(literal l) const { return m_root[l.index()]; }
        bool reaches(literal u, literal v) const { return m_left[u.index()] < m_left[v.index()] && m_right[v.index()] < m_right[u.index()]; }
    };
};

#endif
