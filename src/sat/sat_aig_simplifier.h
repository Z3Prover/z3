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

#include "util/union_find.h"
#include "sat/sat_aig_finder.h"
#include "sat/sat_aig_cuts.h"

namespace sat {

    class aig_simplifier {
    public:
        struct stats {
            unsigned m_num_eqs, m_num_units, m_num_cuts, m_num_xors, m_num_ands, m_num_ites;
            unsigned m_num_calls, m_num_dont_care_reductions;
            stats() { reset(); }
            void reset() { memset(this, 0, sizeof(*this)); }
        };
        struct config {
            bool m_validate;
            bool m_enable_units;
            bool m_enable_dont_cares;
            bool m_add_learned;
            config():
                m_validate(false), 
                m_enable_units(false),
                m_enable_dont_cares(false),
                m_add_learned(true) {}
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
        void cuts2equiv(vector<cut_set> const& cuts);
        void uf2equiv(union_find<> const& uf);
        void assign_unit(literal lit);
        void assign_equiv(cut const& c, literal u, literal v);
        void ensure_validator();
        void validate_unit(literal lit);
        void validate_eq(literal a, literal b);
        void certify_equivalence(literal u, literal v, cut const& c);
        
        /**
         * collect pairs of literal combinations that are impossible
         * base on binary implication graph queries.  Apply the masks
         * on cut sets so to allow detecting equivalences modulo
         * implications.
         */

        enum op_code { pp, pn, np, nn, none };

        struct bin_rel {
            unsigned u, v;
            op_code op;
            bin_rel(unsigned _u, unsigned _v): u(_u), v(_v), op(none) {
                if (u > v) std::swap(u, v);
            }
            bin_rel(): u(UINT_MAX), v(UINT_MAX), op(none) {}

            struct hash {
                unsigned operator()(bin_rel const& p) const { 
                    return mk_mix(p.u, p.v, 1); 
                }
            };
            struct eq {
                bool operator()(bin_rel const& a, bin_rel const& b) const {
                    return a.u == b.u && a.v == b.v;
                }
            };
        };
        hashtable<bin_rel, bin_rel::hash, bin_rel::eq> m_bins;
        
        void add_dont_cares(vector<cut_set> const& cuts);
        void cuts2bins(vector<cut_set> const& cuts);
        void bins2dont_cares();
        void dont_cares2cuts(vector<cut_set> const& cuts);
        bool add_dont_care(cut const & c);
        uint64_t op2dont_care(unsigned i, unsigned j, bin_rel const& p);

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


