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
#include "math/polysat/constraint.h"
#include "math/polysat/solver.h"

namespace polysat {

    class forbidden_intervals {
        solver& s;
        void revert_core(conflict& core);
        void full_interval_conflict(signed_constraint c, vector<signed_constraint> const & side_cond, conflict& core);
        bool get_interval(signed_constraint const& c, pvar v, eval_interval& out_interval, vector<signed_constraint>& side_cond);
        void push_condition(bool is_trivial, pdd const& p, vector<signed_constraint>& side_cond);
        eval_interval to_interval(signed_constraint const& c, bool is_trivial, rational const& coeff,
                                  rational & lo_val, pdd & lo, rational & hi_val, pdd & hi);


        std::tuple<bool, rational, pdd, pdd> linear_decompose(pvar v, pdd const& p, vector<signed_constraint>& out_side_cond);

        bool match_linear1(signed_constraint const& c, 
            rational const& a1, pdd const& b1, pdd const& e1, 
            rational const& a2, pdd const& b2, pdd const& e2,
            eval_interval& interval, vector<signed_constraint>& side_cond);

        bool match_linear2(signed_constraint const& c,
            rational const& a1, pdd const& b1, pdd const& e1,
            rational const& a2, pdd const& b2, pdd const& e2,
            eval_interval& interval, vector<signed_constraint>& side_cond);

        bool match_linear3(signed_constraint const& c,
            rational const& a1, pdd const& b1, pdd const& e1,
            rational const& a2, pdd const& b2, pdd const& e2,
            eval_interval& interval, vector<signed_constraint>& side_cond);

        bool match_linear4(signed_constraint const& c,
            rational const& a1, pdd const& b1, pdd const& e1,
            rational const& a2, pdd const& b2, pdd const& e2,
            eval_interval& interval, vector<signed_constraint>& side_cond);

        bool coefficient_is_01(dd::pdd_manager& m, rational const& r) { return r.is_zero() || r.is_one() || r == m.max_value(); };
    public:
        forbidden_intervals(solver& s) :s(s) {}
        bool perform(pvar v, vector<signed_constraint> const& just, conflict& core);
    };
}
