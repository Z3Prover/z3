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
            unsigned m_num_eqs, m_num_units, m_num_cuts, m_num_xors, m_num_ands, m_num_ites;
            unsigned m_num_calls;
            stats() { reset(); }
            void reset() { memset(this, 0, sizeof(*this)); }
        };
        struct config {
            bool m_full;
            config():m_full(false) {}
        };
    private:
        struct report;
        struct validator;

        solver&  s;
        stats    m_stats;
        config   m_config;
        aig_cuts m_aig_cuts;
        unsigned m_trail_size;
        literal_vector m_lits;
        validator* m_validator;

        void clauses2aig();
        void aig2clauses();
        void ensure_validator();
        void validate_unit(literal lit);
        void validate_eq(literal a, literal b);
        void certify_equivalence(literal u, literal v, cut const& c);
        
        /**
         * collect pairs of literal combinations that are impossible
         * base on binary implication graph queries.
         * Apply the masks on cut sets so to allow detecting 
         * equivalences modulo implications.
         */
        struct var_pair {
            unsigned u, v;
            uint64_t masks[35];
            static unsigned size() { return sizeof(uint64_t)*35; }
            var_pair(unsigned u, unsigned v): u(u), v(v) {
                if (u > v) std::swap(u, v);
            }
            var_pair(): u(UINT_MAX), v(UINT_MAX) {}

            struct hash {
                unsigned operator()(var_pair const& p) const { 
                    return mk_mix(p.u, p.v, 1); 
                }
            };
            struct eq {
                bool operator()(var_pair const& a, var_pair const& b) const {
                    return a.u == b.u && a.v == b.v;
                }
            };
        };
        hashtable<var_pair, var_pair::hash, var_pair::eq> m_pairs;
        
        void collect_pairs(vector<cut_set> const& cuts);
        void add_mask(literal u, literal v, var_pair& p);
        void add_masks_to_pairs();
        void apply_masks();
    public:
        aig_simplifier(solver& s);
        ~aig_simplifier();                
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


