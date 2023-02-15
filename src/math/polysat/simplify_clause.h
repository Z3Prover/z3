/*++
Copyright (c) 2022 Microsoft Corporation

Module Name:

    Clause Simplification

Author:

    Jakob Rath, Nikolaj Bjorner (nbjorner) 2022-08-22

--*/
#pragma once
#include "math/polysat/constraint.h"
#include "math/polysat/forbidden_intervals.h"

namespace polysat {

    class solver;
    
    struct trailing_bits {
        unsigned length;
        rational bits;
        bool positive;
        unsigned src_idx;
    };
    struct single_bit {
        bool positive;
        unsigned position;
        unsigned src_idx;
    };

    class simplify_clause {

        struct subs_entry : fi_record {
            optional<pdd>  var;
            bool subsuming = false;
            bool valid = false;
        };

        solver& s;
        vector<subs_entry> m_entries;
        bool_vector m_bools;

        bool try_remove_equations(clause& cl);
        bool try_recognize_bailout(clause& cl);
        bool try_equal_body_subsumptions(clause& cl);
        bool try_bit_subsumptions(clause& cl);

        void prepare_subs_entry(subs_entry& entry, signed_constraint c);

        pdd abstract(pdd const& p, pdd& v);
        
        clause_ref make_asserting(clause& cl, pvar z, rational z_val);
        void find_implied_constraint(signed_constraints const& cz, pvar z, rational z_val, sat::literal_vector& out_lits);
        void find_implied_constraint_sat(signed_constraints const& cz, pvar z, rational z_val, sat::literal_vector& out_lits);

    public:
        simplify_clause(solver& s);

        bool apply(clause& cl);
        
        static bool get_trailing_mask(pdd lhs, pdd rhs, pdd& p, trailing_bits& mask, bool pos);
        static bool get_bit(const pdd& lhs, const pdd& rhs, pdd& p, single_bit& bit, bool pos);
    };

}
