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
#pragma once

#include "util/statistics.h"
#include "util/params.h"
#include "sat/sat_types.h"
#include "sat/sat_big.h"

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

        big        m_big;

        void reduce_tr();
        unsigned reduce_tr(bool learned);

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
        void init_big(bool learned) { m_big.init(m_solver, learned); }
        void ensure_big(bool learned) { m_big.ensure_big(m_solver, learned); }
        int get_left(literal l) const { return m_big.get_left(l); }
        int get_right(literal l) const { return m_big.get_right(l); }
        bool connected(literal u, literal v) const { return m_big.connected(u, v); }
    };
};

