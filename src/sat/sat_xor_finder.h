/*++
  Copyright (c) 2020 Microsoft Corporation

  Module Name:

   sat_xor_finder.h

  Abstract:
   
    xor finder

  Author:

    Nikolaj Bjorner 2020-01-02

  Notes:
  
    Based on xor extraction paper by Meel & Soos, AAAI 2018.

  --*/

#pragma once

#include "util/params.h"
#include "util/statistics.h"
#include "sat/sat_clause.h"
#include "sat/sat_types.h"
#include "sat/sat_solver.h"

namespace sat {

    class xor_finder {
        solver& s;
        struct clause_filter {
            unsigned m_filter;
            clause*  m_clause;            
            clause_filter(unsigned f, clause* cp):
                m_filter(f), m_clause(cp) {}
        };
        unsigned                m_max_xor_size;
        vector<svector<clause_filter>>   m_clause_filters;      // index of clauses.
        unsigned                m_combination;  // bit-mask of parities that have been found
        vector<bool_vector>     m_parity;       // lookup parity for clauses
        clause_vector           m_clauses_to_remove;    // remove clauses that become xors
        unsigned_vector         m_var_position; // position of var in main clause
        literal_vector          m_clause;       // reference clause with literals sorted according to main clause
        unsigned_vector         m_missing;      // set of indices not occurring in clause.
        clause_vector           m_removed_clauses;
        std::function<void (literal_vector const& lits)> m_on_xor;

        void set_combination(unsigned mask);
        inline bool get_combination(unsigned mask) const { return (m_combination & (1 << mask)) != 0; }
        void extract_xor(clause& c);
        void add_xor(bool parity, clause& c);
        bool extract_xor(bool parity, clause& c, literal l1, literal l2);
        bool extract_xor(bool parity, clause& c, clause& c2);
        bool update_combinations(clause& c, bool parity, unsigned mask);
        void init_parity();
        void init_clause_filter();
        void init_clause_filter(clause_vector& clauses);
        unsigned get_clause_filter(clause& c);

    public:
        xor_finder(solver& s) : s(s), m_max_xor_size(5) { init_parity(); }

        void set(std::function<void (literal_vector const& lits)>& f) { m_on_xor = f; }

        bool parity(unsigned i, unsigned j) const { return m_parity[i][j]; }
        unsigned max_xor_size() const { return m_max_xor_size; }

        void operator()(clause_vector& clauses);        
        clause_vector const& removed_clauses() const { return m_removed_clauses; }
    };
}
