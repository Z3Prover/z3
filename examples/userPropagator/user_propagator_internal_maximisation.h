#pragma once

#include "user_propagator_with_theory.h"

class user_propagator_internal_maximisation : public user_propagator_with_theory {

    z3::expr manhattanSum;

public:

    int best = -1;

    user_propagator_internal_maximisation(z3::solver *s, std::unordered_map<z3::expr, unsigned> &idMapping, unsigned board, z3::expr_vector queens)
            : user_propagator_with_theory(s, idMapping, board),
              manhattanSum(s->ctx().bv_val(0, queens[0].get_sort().bv_size())) {
        for (int i = 1; i < queens.size(); i++) {
            manhattanSum = manhattanSum + z3::ite(z3::uge(queens[i], queens[i - 1]), queens[i] - queens[i - 1], queens[i - 1] - queens[i]);
        }
    }

    void final() override {

        int current = 0;
        for (unsigned i = 1; i < board; i++) {
            current += abs((signed) currentModel[i] - (signed) currentModel[i - 1]);
        }
        best = std::max(current, best);
        this->propagate(z3::expr_vector(ctx()), z3::ugt(manhattanSum, best));
    }
};