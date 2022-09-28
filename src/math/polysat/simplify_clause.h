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

    class simplify_clause {

        struct subs_entry : fi_record {
            optional<pdd>  var;
            bool subsuming = false;
            bool valid = false;
        };

        solver& s;
        vector<subs_entry> m_entries;

        bool try_recognize_bailout(clause& cl);
        bool try_equal_body_subsumptions(clause& cl);

        void prepare_subs_entry(subs_entry& entry, signed_constraint c);

        pdd abstract(pdd const& p, pdd& v);
        
        clause_ref make_asserting(clause& cl, pvar z, rational z_val);
        void find_implied_constraint(signed_constraints const& cz, pvar z, rational z_val, sat::literal_vector& out_lits);
        void find_implied_constraint_sat(signed_constraints const& cz, pvar z, rational z_val, sat::literal_vector& out_lits);

    public:
        simplify_clause(solver& s);

        bool apply(clause& cl);
    };

}
