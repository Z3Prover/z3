#pragma once

#include "user_propagator.h"

class user_propagator_subquery_maximisation : public user_propagator {

    z3::expr assertion;
    z3::expr_vector queens;
    z3::expr manhattanSum;

public:

    user_propagator_subquery_maximisation(z3::solver *s, std::unordered_map<z3::expr, unsigned> &idMapping, unsigned board, z3::expr_vector queens)
            : user_propagator(s, idMapping, board),
              assertion(mk_and(s->assertions())),
              queens(queens), manhattanSum(s->ctx().bv_val(0, queens[0].get_sort().bv_size())) {

        for (int i = 1; i < queens.size(); i++) {
            manhattanSum = manhattanSum + z3::ite(z3::uge(queens[i], queens[i - 1]), queens[i] - queens[i - 1], queens[i - 1] - queens[i]);
        }
    }

    void final() override {

        int max1 = 0;
        for (unsigned i = 1; i < board; i++) {
            max1 += abs((signed) currentModel[i] - (signed) currentModel[i - 1]);
        }
        z3::expr_vector vec(ctx());

        int max2 = 0;
        z3::solver subquery(ctx(), z3::solver::simple());

        subquery.add(assertion);
        subquery.add(z3::ugt(manhattanSum, max1));
        if (subquery.check() == z3::unsat)
            return; // model is already maximal

        z3::model counterExample = subquery.get_model();

        int prev, curr = -1;

        for (int i = 0; i < queens.size(); i++) {
            prev = curr;
            curr = counterExample.eval(queens[i]).get_numeral_int();
            if (i == 0) continue;
            max2 += abs(curr - prev);
        }
        this->propagate(vec, z3::uge(manhattanSum, max2));
    }
};