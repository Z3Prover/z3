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

#pragma once

#include "util/params.h"
#include "util/statistics.h"
#include "sat/sat_clause.h"
#include "sat/sat_types.h"
#include "sat/sat_big.h"

namespace sat {

    class solver;

    class aig_finder {
        solver& s;
        big                     m_big;
        literal_vector          m_ands; 
        std::function<void (literal head, literal_vector const& ands)> m_on_aig;
        std::function<void (literal head, literal cond, literal th, literal el)> m_on_if;
        bool implies(literal a, literal b);
        bool find_aig(clause& c);
        void find_ifs(clause_vector& clauses);
        void find_aigs(clause_vector& clauses);
        void validate_and(literal head, literal_vector const& ands, clause const& c);
        void validate_if(literal x, literal c, literal t, literal e, clause const& c0, clause const* c1, clause const* c2, clause const* c3);
        void validate_clause(literal x, literal y, literal z, vector<literal_vector> const& clauses);
        void validate_clause(literal_vector const& clause, vector<literal_vector> const& clauses);

    public:
        aig_finder(solver& s);
        void set(std::function<void (literal head, literal_vector const& ands)> const& f) { m_on_aig = f; }
        void set(std::function<void (literal head, literal cond, literal th, literal el)> const& f) { m_on_if = f; }
        void operator()(clause_vector& clauses);
    };
}
