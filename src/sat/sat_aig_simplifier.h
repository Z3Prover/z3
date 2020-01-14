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
            bool m_enable_implies;
            bool m_add_learned;
            config():
                m_validate(false), 
                m_enable_units(false),
                m_enable_dont_cares(false),
                m_enable_implies(false),
                m_add_learned(true) {}
        };
    private:
        struct report;
        struct validator;

        /**
         * collect pairs of literal combinations that are impossible
         * base on binary implication graph queries.  Apply the masks
         * on cut sets so to allow detecting equivalences modulo
         * implications.
         *
         * The encoding is as follows:
         * a or b   -> op = nn because (~a & ~b) is a don't care
         * ~a or b  -> op = pn because (a & ~b)  is a don't care
         * a or ~b  -> op = np because (~a & b)  is a don't care
         * ~a or ~b -> op = pp because (a & b)   is a don't care
         *
         */

        enum op_code { pp, pn, np, nn, none };

        struct bin_rel {
            unsigned u, v;
            op_code op;
            bin_rel(unsigned _u, unsigned _v): u(_u), v(_v), op(none) {
                if (u > v) std::swap(u, v);
            }
            // convert binary clause into a bin-rel
            bin_rel(literal _u, literal _v): u(_u.var()), v(_v.var()), op(none) {
                if (_u.sign() && _v.sign()) op = pp;
                else if (_u.sign()) op = pn;
                else if (_v.sign()) op = np;
                else op = nn;
                if (u > v) {
                    std::swap(u, v);
                    if (op == np) op = pn;
                    else if (op == pn) op = np;
                }
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
            void to_binary(literal& lu, literal& lv) const {
                switch (op) {
                case pp: lu = literal(u, true); lv = literal(v, true); break;
                case pn: lu = literal(u, true); lv = literal(v, false); break;
                case np: lu = literal(u, false); lv = literal(v, true); break;
                case nn: lu = literal(u, false); lv = literal(v, false); break;
                default: UNREACHABLE(); break;
                }
            }
        };


        solver&  s;
        stats    m_stats;
        config   m_config;
        aig_cuts m_aig_cuts;
        unsigned m_trail_size;
        literal_vector m_lits;
        validator* m_validator;
        hashtable<bin_rel, bin_rel::hash, bin_rel::eq> m_bins;

        void clauses2aig();
        void aig2clauses();
        void cuts2equiv(vector<cut_set> const& cuts);
        void cuts2implies(vector<cut_set> const& cuts);
        void uf2equiv(union_find<> const& uf);
        void assign_unit(cut const& c, literal lit);
        void assign_equiv(cut const& c, literal u, literal v);
        void learn_implies(big& big, cut const& c, literal u, literal v);
        void ensure_validator();
        void validate_unit(literal lit);
        void validate_eq(literal a, literal b);
        void certify_unit(literal u, cut const& c);
        void certify_implies(literal u, literal v, cut const& c);
        void certify_equivalence(literal u, literal v, cut const& c);
        void track_binary(literal u, literal v);
        void untrack_binary(literal u, literal v);
        void track_binary(bin_rel const& p);
        void untrack_binary(bin_rel const& p);        

        
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


