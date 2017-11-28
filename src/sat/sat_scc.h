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

        void get_dfs_num(svector<int>& dfs, bool learned);
        void reduce_tr();
        bool reduce_tr(bool learned);
        bool reduce_tr(svector<int> const& dfs, bool learned);

    public:
        scc(solver & s, params_ref const & p);
        unsigned operator()();

        void updt_params(params_ref const & p);
        static void collect_param_descrs(param_descrs & d);

        void collect_statistics(statistics & st) const;
        void reset_statistics();
    };
};

#endif
