/*++
Copyright (c) 2011 Microsoft Corporation

Module Name:

    sat_asymm_branch.h

Abstract:

    SAT solver asymmetric branching

Author:

    Leonardo de Moura (leonardo) 2011-05-30.

Revision History:

--*/
#ifndef SAT_ASYMM_BRANCH_H_
#define SAT_ASYMM_BRANCH_H_

#include"sat_types.h"
#include"statistics.h"
#include"params.h"

namespace sat {
    class solver;

    class asymm_branch {
        struct report;
        
        solver & s;
        int      m_counter;

        // config
        bool                   m_asymm_branch;
        unsigned               m_asymm_branch_rounds;
        unsigned               m_asymm_branch_limit;

        // stats
        unsigned m_elim_literals;

        bool process(clause & c);
    public:
        asymm_branch(solver & s, params_ref const & p);

        void operator()(bool force = false);

        void updt_params(params_ref const & p);
        static void collect_param_descrs(param_descrs & d);

        void collect_statistics(statistics & st) const;
        void reset_statistics();

        void dec(unsigned c) { m_counter -= c; }
    };

};

#endif
