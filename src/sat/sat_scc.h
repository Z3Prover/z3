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
#ifndef _SAT_SCC_H_
#define _SAT_SCC_H_

#include"sat_types.h"
#include"statistics.h"
#include"params.h"

namespace sat {
    class solver;

    class scc {
        struct report;
        solver &   m_solver;
        // config
        bool       m_scc;
        // stats
        unsigned   m_num_elim;
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
