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

#include "sat/sat_types.h"
#include "util/statistics.h"
#include "util/params.h"

namespace sat {
    class solver;
    class scoped_detach;

    class asymm_branch {
        struct report;
        
        solver & s;
        int64      m_counter;
        random_gen m_rand;

        // config
        bool                   m_asymm_branch;
        bool                   m_asymm_branch_all;
        int64                  m_asymm_branch_limit;

        // stats
        unsigned m_elim_literals;

        bool process(clause & c);
        
        bool process_all(clause & c);
        
        bool flip_literal_at(clause const& c, unsigned flip_index, unsigned& new_sz);
        
        bool cleanup(scoped_detach& scoped_d, clause& c, unsigned skip_index, unsigned new_sz);

        bool propagate_literal(clause const& c, literal l);

    public:
        asymm_branch(solver & s, params_ref const & p);

        void operator()(bool force = false);

        void updt_params(params_ref const & p);
        static void collect_param_descrs(param_descrs & d);

        void collect_statistics(statistics & st) const;
        void reset_statistics();

        inline void dec(unsigned c) { m_counter -= c; }
    };

};

#endif
