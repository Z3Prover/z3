/*++
  Copyright (c) 2019 Microsoft Corporation

  Module Name:

   sat_spr.h

  Abstract:
   
    Inprocessing step for creating SPR binary clauses.

  Author:

    Nikolaj Bjorner, Marijn Heule 2019-4-29

  Notes:
  

  --*/
#ifndef _SAT_BINSPR_
#define _SAT_BINSPR_

#include "util/params.h"
#include "util/statistics.h"
#include "sat/sat_clause.h"
#include "sat/sat_types.h"

namespace sat {
    class solver;
    class big;

    class binspr {
        solver& s;
        svector<std::pair<literal, literal>> m_bin_clauses;
        unsigned                             m_stopped_at;
        vector<clause_vector>                m_use_list;
        unsigned                             m_limit1, m_limit2;

        struct report;

        void process(big& big, literal lit1);
        void check_spr(literal lit1, literal lit2);
        bool binary_is_unit_implied(literal lit);
        bool clause_is_unit_implied(literal lit1, literal lit2, clause& c);
        
    public:

        binspr(solver& s, params_ref const& p): s(s), m_stopped_at(0), m_limit1(500), m_limit2(100) {}

        ~binspr() {}

        void operator()();

        void updt_params(params_ref const& p) {}

        void collect_statistics(statistics& st) const {} 

    };
}

#endif
