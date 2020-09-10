/*++
  Copyright (c) 2020 Microsoft Corporation

  Module Name:

   sat_cut_simplifier.h

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

    class cut_simplifier {
    public:
        struct stats {
            unsigned m_num_eqs, m_num_units, m_num_cuts, m_num_xors, m_num_ands, m_num_ites;
            unsigned m_xxors, m_xands, m_xites, m_xluts;                         // extrated gates
            unsigned m_num_calls, m_num_dont_care_reductions, m_num_learned_implies;
            stats() { reset(); }
            void reset() { memset(this, 0, sizeof(*this)); }
        };
        struct config {
            bool m_enable_units;            // enable learning units
            bool m_enable_dont_cares;       // enable applying don't cares to LUTs
            bool m_learn_implies;           // learn binary clauses
            bool m_learned2aig;             // add learned clauses to AIGs used by cut-set enumeration
            bool m_validate_cuts;           // enable direct validation of generated cuts
            bool m_validate_lemmas;         // enable direct validation of learned lemmas 
            bool m_simulate_eqs;            // use symbolic simulation to control size of cutsets.
            config():
                m_enable_units(true),
                m_enable_dont_cares(true),
                m_learn_implies(false),
                m_learned2aig(true),
                m_validate_cuts(false), 
                m_validate_lemmas(false),
                m_simulate_eqs(false) {}
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

        enum class op_code { pp, pn, np, nn, none };

        struct bin_rel {
            unsigned u, v;
            op_code op;
            bin_rel(unsigned _u, unsigned _v): u(_u), v(_v), op(op_code::none) {
                if (u > v) std::swap(u, v);
            }
            // convert binary clause into a bin-rel
            bin_rel(literal _u, literal _v): u(_u.var()), v(_v.var()), op(op_code::none) {
                if (_u.sign() && _v.sign()) op = op_code::pp;
                else if (_u.sign()) op = op_code::pn;
                else if (_v.sign()) op = op_code::np;
                else op = op_code::nn;
                if (u > v) {
                    std::swap(u, v);
                    if (op == op_code::np) op = op_code::pn;
                    else if (op == op_code::pn) op = op_code::np;
                }
            }
            bin_rel(): u(UINT_MAX), v(UINT_MAX), op(op_code::none) {}

            struct hash {
                unsigned operator()(bin_rel const& p) const { 
                    return p.u + 65599*p.v; // Weinberger's should be a bit cheaper mk_mix(p.u, p.v, 1); 
                }
            };
            struct eq {
                bool operator()(bin_rel const& a, bin_rel const& b) const {
                    return a.u == b.u && a.v == b.v;
                }
            };
            void to_binary(literal& lu, literal& lv) const {
                switch (op) {
                case op_code::pp: lu = literal(u, true); lv = literal(v, true); break;
                case op_code::pn: lu = literal(u, true); lv = literal(v, false); break;
                case op_code::np: lu = literal(u, false); lv = literal(v, true); break;
                case op_code::nn: lu = literal(u, false); lv = literal(v, false); break;
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
        void simulate_eqs();
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
        cut_simplifier(solver& s);
        ~cut_simplifier();                
        void operator()();
        void collect_statistics(statistics& st) const;

        /**
         * The clausifier may know that some literal is defined as a 
         * function of other literals. This API is exposed so that 
         * the clausifier can instrument the simplifier with an initial
         * AIG.
         * set_root is issued from the equivalence finder.
         */
        void add_and(literal head, unsigned sz, literal const* args);
        void add_or(literal head, unsigned sz, literal const* args);
        void add_xor(literal head, unsigned sz, literal const* args);
        void add_ite(literal head, literal c, literal t, literal e);
        void add_iff(literal head, literal l1, literal l2);
        void set_root(bool_var v, literal r);
    };
}


