/*++
Copyright (c) 2021 Microsoft Corporation

Module Name:

    Conflict explanation using forbidden intervals as described in
    "Solving bitvectors with MCSAT: explanations from bits and pieces"
    by S. Graham-Lengrand, D. Jovanovic, B. Dutertre.

Author:

    Nikolaj Bjorner (nbjorner) 2021-03-19
    Jakob Rath 2021-04-6

--*/
#pragma once
#include "math/polysat/conflict.h"

namespace polysat {

    class solver;

    class forbidden_intervals {
        solver& s;

        void push_eq(bool is_trivial, pdd const& p, vector<signed_constraint>& side_cond);
        eval_interval to_interval(signed_constraint const& c, bool is_trivial, rational& coeff,
                                  rational & lo_val, pdd & lo, rational & hi_val, pdd & hi);


        std::tuple<bool, rational, pdd, pdd> linear_decompose(pvar v, pdd const& p, vector<signed_constraint>& out_side_cond);

        bool match_linear1(signed_constraint const& c,
            rational const& a1, pdd const& b1, pdd const& e1,
            rational const& a2, pdd const& b2, pdd const& e2,
            fi_record& fi);

        bool match_linear2(signed_constraint const& c,
            rational const & a1, pdd const& b1, pdd const& e1,
            rational const & a2, pdd const& b2, pdd const& e2,
            fi_record& fi);

        bool match_linear3(signed_constraint const& c,
            rational const & a1, pdd const& b1, pdd const& e1,
            rational const & a2, pdd const& b2, pdd const& e2,
            fi_record& fi);

        void add_non_unit_side_conds(fi_record& fi, pdd const& b1, pdd const& e1, pdd const& b2, pdd const& e2);

    public:
        forbidden_intervals(solver& s) :s(s) {}
        bool get_interval(signed_constraint const& c, pvar v, fi_record& fi);
    };
}
