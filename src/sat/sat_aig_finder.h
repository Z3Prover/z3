/*++
  Copyright (c) 2020 Microsoft Corporation

  Module Name:

   sat_aig_finder.h

  Abstract:
   
    extract AIG definitions from clauses.
    An example AIG clause is:
       head \/ l1 \/ l2
    such that 
       ~l1 /\ ~l2 => head
       head => ~l1, head => ~l2

  Author:

    Nikolaj Bjorner 2020-01-02

  Notes:
  
    AIG finder
  --*/

#pragma once;

#include "util/params.h"
#include "util/statistics.h"
#include "sat/sat_clause.h"
#include "sat/sat_types.h"
#include "sat/sat_solver.h"
#include "sat/sat_big.h"

namespace sat {

    class aig_finder {
        solver& s;
        big                     m_big;
        literal_vector          m_ands; 
        std::function<void (literal head, literal_vector const& ands, clause& orig)> m_aig_def;
        bool implies(literal a, literal b);
        bool find_aig(clause& c);
        bool find_if(clause& c);

    public:
        aig_finder(solver& s) : s(s), m_big(s.rand()) {}
        ~aig_finder() {}                
        void set(std::function<void (literal head, literal_vector const& ands, clause& orig)>& f) { m_aig_def = f; }
        void operator()(clause_vector const& clauses);
    };
}
