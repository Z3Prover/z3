/*++
  Copyright (c) 2019 Microsoft Corporation

  Module Name:

   sat_binspr.h

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

    class binspr {
        solver& s;
        unsigned                             m_bin_clauses;
        unsigned                             m_stopped_at;
        vector<clause_vector>                m_use_list;
        unsigned                             m_limit1, m_limit2;
        literal_vector                       m_units;
        svector<std::pair<literal, literal>> m_bins;

        struct report;

        void reset_g(literal lit1, literal lit2);
        bool add_g(literal lit1);
        bool add_g(literal lit1, literal lit2);
        void block_binary(literal lit1, literal lit2, bool learned);
        void check_spr(literal lit1);
        void check_spr(literal lit1, literal lit2);
        bool binary_are_unit_implied(literal lit1, literal lit2);
        bool clauses_are_unit_implied(literal lit1, literal lit2);
        bool clause_is_unit_implied(literal lit1, literal lit2, clause& c);
        
    public:

        binspr(solver& s, params_ref const& p): s(s), m_stopped_at(0), m_limit1(1000), m_limit2(300) {}

        ~binspr() {}

        void operator()();

        void updt_params(params_ref const& p) {}

        void collect_statistics(statistics& st) const {} 

    };
}

#endif
