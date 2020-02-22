/*++
  Copyright (c) 2020 Microsoft Corporation

  Module Name:

   sat_lut_finder.h

  Abstract:
   
    lut finder

  Author:

    Nikolaj Bjorner 2020-02-03

  Notes:
  
    Find LUT with small input fan-ins

  --*/

#pragma once

#include "util/params.h"
#include "util/statistics.h"
#include "sat/sat_clause.h"
#include "sat/sat_types.h"
#include "sat/sat_solver.h"

namespace sat {

    class lut_finder {
        solver& s;
        struct clause_filter {
            unsigned m_filter;
            clause*  m_clause;            
            clause_filter(unsigned f, clause* cp):
                m_filter(f), m_clause(cp) {}
        };
        typedef svector<bool> bool_vector;
        unsigned                m_max_lut_size;
        vector<svector<clause_filter>>   m_clause_filters;  // index of clauses.
        uint64_t                m_combination;              // bit-mask of parities that have been found
        unsigned                m_num_combinations;
        clause_vector           m_clauses_to_remove;        // remove clauses that become luts
        unsigned_vector         m_var_position;             // position of var in main clause
        bool_var_vector         m_vars;                     // reference to variables being tested for LUT
        literal_vector          m_clause;                   // reference clause with literals sorted according to main clause
        unsigned_vector         m_missing;                  // set of indices not occurring in clause.
        uint64_t                m_masks[7];
        clause_vector           m_removed_clauses;
        std::function<void (uint64_t, svector<bool_var> const& vars, bool_var v)> m_on_lut;

        void set_combination(unsigned mask);
        inline bool get_combination(unsigned mask) const { return (m_combination & (1ull << mask)) != 0; }
        bool lut_is_defined(unsigned sz);
        bool lut_is_defined(unsigned i, unsigned sz);
        uint64_t convert_combination(bool_var_vector& vars, bool_var& v);
        void check_lut(clause& c);
        void add_lut();
        bool extract_lut(literal l1, literal l2);
        bool extract_lut(clause& c2);
        bool update_combinations(unsigned mask);
        void init_clause_filter();
        void init_clause_filter(clause_vector& clauses);
        unsigned get_clause_filter(clause const& c);
        std::ostream& display_mask(std::ostream& out, uint64_t mask, unsigned sz) const;

    public:
        lut_finder(solver& s) : s(s), m_max_lut_size(5) { }
        ~lut_finder() {}        

        void set(std::function<void (uint64_t, bool_var_vector const&, bool_var)>& f) { m_on_lut = f; }

        unsigned max_lut_size() const { return m_max_lut_size; }
        void operator()(clause_vector& clauses);        

    };
}
