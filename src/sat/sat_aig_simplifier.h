/*++
  Copyright (c) 2020 Microsoft Corporation

  Module Name:

   sat_aig_simplifier.h

  Abstract:
   
    extract AIG definitions from clauses
    Perform cut-set enumeration to identify equivalences.

  Author:

    Nikolaj Bjorner 2020-01-02

  --*/

#pragma once

#include "sat/sat_aig_finder.h"
#include "sat/sat_aig_cuts.h"

namespace sat {

    class aig_simplifier {
    public:
        struct stats {
            unsigned m_num_eqs, m_num_cuts, m_num_xors, m_num_ands, m_num_ites;
            stats() { reset(); }
            void reset() { memset(this, 0, sizeof(*this)); }
        };
    private:
        solver&  s;
        stats    m_stats;
        aig_cuts m_aig_cuts;
        unsigned m_trail_size;
        literal_vector m_lits;

        struct report;
        void clauses2aig();
        void aig2clauses();
    public:
        aig_simplifier(solver& s);
        ~aig_simplifier() {}                
        void operator()();
        void collect_statistics(statistics& st) const;

        void add_and(literal head, unsigned sz, literal const* args);
        void add_or(literal head, unsigned sz, literal const* args);
        void add_xor(literal head, unsigned sz, literal const* args);
        void add_ite(literal head, literal c, literal t, literal e);
        void add_iff(literal head, literal l1, literal l2);
        void set_root(bool_var v, literal r);
    };
}


