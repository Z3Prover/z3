#pragma once

#include "user_propagator.h"

class user_propagator_with_theory : public user_propagator {

public:

    user_propagator_with_theory(z3::context &c, std::unordered_map<z3::expr, unsigned> &idMapping, unsigned board)
            : user_propagator(c, idMapping, board) {}

    user_propagator_with_theory(z3::solver *s, std::unordered_map<z3::expr, unsigned> &idMapping, unsigned board)
            : user_propagator(s, idMapping, board) {}

    void fixed(z3::expr const &ast, z3::expr const &value) override {
        unsigned queenId = queenToY[ast];
        unsigned queenPos = bvToInt(value);

        if (queenPos >= board) {
            z3::expr_vector conflicting(ast.ctx());
            conflicting.push_back(ast);
            this->conflict(conflicting);
            return;
        }

        for (const z3::expr &fixed: fixedValues) {
            unsigned otherId = queenToY[fixed];
            unsigned otherPos = currentModel[queenToY[fixed]];

            if (queenPos == otherPos) {
                z3::expr_vector conflicting(ast.ctx());
                conflicting.push_back(ast);
                conflicting.push_back(fixed);
                this->conflict(conflicting);
                continue;
            }
            int diffY = abs((int) queenId - (int) otherId);
            int diffX = abs((int) queenPos - (int) otherPos);
            if (diffX == diffY) {
                z3::expr_vector conflicting(ast.ctx());
                conflicting.push_back(ast);
                conflicting.push_back(fixed);
                this->conflict(conflicting);
            }
        }

        fixedValues.push_back(ast);
        currentModel[queenToY[ast]] = queenPos;
    }
};