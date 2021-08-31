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
#pragma once

#include "util/params.h"
#include "util/statistics.h"
#include "sat/sat_clause.h"
#include "sat/sat_types.h"

namespace sat {
    class solver;

    class binspr {
        enum states {
            unit                = 0xA,  // 1010 
            unit_or_other_nunit = 0xB,  // 1011
            either              = 0xE,  // 1110    
            nand                = 0x7,  // 0111
            not_pr              = 0x0
        };

        solver&                              m_solver;
        scoped_ptr<solver>                   s;
        unsigned                             m_bin_clauses{ 0 };
        unsigned                             m_stopped_at{ 0 };
        vector<clause_vector>                m_use_list;
        unsigned                             m_limit1{ 0 }, m_limit2{ 0 };
        bool_vector                        m_mark, m_mark2;
        literal_vector                       m_must_candidates, m_may_candidates;
        unsigned                             m_state{ 0 };

        void init_g() { m_state = 0x7; }
        void g_add_binary(literal l1, literal l2, bool flip2);
        void g_add_unit(literal l1, literal l2);      // l1 is a unit
        bool g_is_sat() { return m_state != 0; }

        void init_g(literal p, literal q, literal u, literal v);


        struct report;

        void block_binary(literal lit1, literal lit2, bool learned);
        void double_lookahead();
        
        void check_spr_single_lookahead(literal lit);
        void check_spr(literal lit1);
        void check_spr(literal lit1, literal lit2);
        bool check_spr(literal p, literal q, literal s, literal r);
        void binary_are_unit_implied(literal lit1, literal lit2);
        void clauses_are_unit_implied(literal lit1, literal lit2);
        void clause_is_unit_implied(literal lit1, literal lit2, clause& c);
        bool is_used(literal lit) const;
        void update_candidates(bool& first, unsigned sz1);
        void collect_candidates(literal lit, literal const* begin, literal const* end);
        void strengthen_clause(literal lit, literal const* begin, literal const* end);

        bool_var m_p{ 0 }, m_q{ 0 }, m_u{ 0 }, m_v{ 0 };
        lbool m_vals[4];

        void algorithm2();
        void algorithm2(literal lit, clause const& c);
        void clear_alpha();
        void add_touched();
        bool touch(literal p);
        void binary_are_unit_implied(literal p);
        void clauses_are_unit_implied(literal p);
        void clause_is_unit_implied(clause const& c);
        static const unsigned max_lits = 5; // = log(32)
        unsigned m_true[max_lits], m_false[max_lits];
        unsigned mk_function(svector<lbool> const& lits);
        void mk_masks();
        unsigned mk_mask(unsigned i);

        std::ostream& display_mask(std::ostream& out, unsigned mask) const;

    public:

        binspr(solver& s): m_solver(s), m_stopped_at(0), m_limit1(1000), m_limit2(300) {
            memset(m_true, 0, sizeof(unsigned) * max_lits);
            memset(m_false, 0, sizeof(unsigned) * max_lits);
        }

        void operator()();

        void updt_params(params_ref const& p) {}

        void collect_statistics(statistics& st) const {} 

    };
}

