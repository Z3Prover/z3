#pragma once

#include "common.h"

class user_propagator_created_maximisation : public z3::user_propagator_base {


    std::unordered_map<z3::expr, z3::expr_vector> argToFcts;
    std::unordered_map<z3::expr, z3::expr_vector> fctToArgs;

    std::unordered_map<z3::expr, unsigned> currentModel;
    z3::expr_vector fixedValues;
    std::vector<unsigned> fixedCnt;

    user_propagator_created_maximisation* childPropagator = nullptr;
    user_propagator_created_maximisation* parentPropagator = nullptr;

    int board;
    int nesting; // Just for logging (0 ... main solver; 1 ... sub-solver)

public:

    user_propagator_created_maximisation(z3::context &c, user_propagator_created_maximisation* parentPropagator, unsigned board, int nesting) :
            z3::user_propagator_base(c), fixedValues(c), parentPropagator(parentPropagator), board(board), nesting(nesting) {

        this->register_fixed();
        this->register_final();
        this->register_created();
    }

    user_propagator_created_maximisation(z3::solver *s, unsigned board) :
            z3::user_propagator_base(s), fixedValues(s->ctx()), board(board), nesting(0) {

        this->register_fixed();
        this->register_final();
        this->register_created();
    }

    ~user_propagator_created_maximisation() {
        delete childPropagator;
    }

    void final() override {
        WriteLine("Final (" + to_string(nesting) + ")");
    }

    void push() override {
        WriteLine("Push (" + to_string(nesting) + ")");
        fixedCnt.push_back((unsigned) fixedValues.size());
    }

    void pop(unsigned num_scopes) override {
        WriteLine("Pop (" + to_string(nesting) + ")");
        for (unsigned i = 0; i < num_scopes; i++) {
            unsigned lastCnt = fixedCnt.back();
            fixedCnt.pop_back();
            for (auto j = fixedValues.size(); j > lastCnt; j--) {
                currentModel.erase(fixedValues[j - 1]);
            }
            fixedValues.resize(lastCnt);
        }
    }

    void checkValidPlacement(std::vector<z3::expr_vector> &conflicts, const z3::expr &fct, const z3::expr_vector &args, const std::vector<unsigned> &argValues, int pos) {
        unsigned queenId = pos;
        unsigned queenPos = argValues[pos];
        z3::expr queenPosExpr = args[pos];

        if (queenPos >= board) {
            z3::expr_vector conflicting(ctx());
            conflicting.push_back(fct);
            conflicting.push_back(queenPosExpr);
            conflicts.push_back(conflicting);
            return;
        }

        for (unsigned otherId = 0; otherId < argValues.size(); otherId++) {
            if (otherId == pos)
                continue;

            unsigned otherPos = argValues[otherId];
            z3::expr otherPosExpr = args[otherId];

            if (otherPos == (unsigned)-1)
                continue; // We apparently do not have this value

            if (queenPos == otherPos) {
                z3::expr_vector conflicting(ctx());
                conflicting.push_back(fct);
                conflicting.push_back(queenPosExpr);
                conflicting.push_back(otherPosExpr);
                conflicts.push_back(conflicting);
            }
            int diffY = abs((int) queenId - (int) otherId);
            int diffX = abs((int) queenPos - (int) otherPos);
            if (diffX == diffY) {
                z3::expr_vector conflicting(ctx());
                conflicting.push_back(fct);
                conflicting.push_back(queenPosExpr);
                conflicting.push_back(otherPosExpr);
                conflicts.push_back(conflicting);
            }
        }
    }

    unsigned getValues(const z3::expr &fct, std::vector<unsigned> &argValues) const {
        z3::expr_vector args = fctToArgs.at(fct);
        unsigned fixed = 0;
        for (const z3::expr &arg: args) {
            if (currentModel.contains(arg)) {
                argValues.push_back(currentModel.at(arg));
                fixed++;
            }
            else
                argValues.push_back((unsigned) -1); // no value so far
        }
        return fixed;
    }


    user_propagator_base *fresh(z3::context &ctx) override {
        WriteLine("Fresh context");
        childPropagator = new user_propagator_created_maximisation(ctx, this, board, nesting + 1);
        return childPropagator;
    }

    void fixed(const z3::expr &expr, const z3::expr &value) override {
        // Could be optimized!
        WriteLine("Fixed (" + to_string(nesting) + ") " + expr.to_string() + " to " + value.to_string());
        unsigned v = value.is_true() ? 1 : (value.is_false() ? 0 : value.get_numeral_uint());
        currentModel[expr] = v;
        fixedValues.push_back(expr);

        z3::expr_vector effectedFcts(ctx());
        bool fixedFct = fctToArgs.contains(expr);

        if (fixedFct) {
            // fixed the value of a function
            effectedFcts.push_back(expr);
        }
        else {
            // fixed the value of a function's argument
            effectedFcts = argToFcts.at(expr);
        }

        for (const z3::expr& fct : effectedFcts) {
            if (!currentModel.contains(fct))
                // we do not know yet whether to expect a valid or invalid placement
                continue;

            std::vector<unsigned> values;
            unsigned fixedArgsCnt = getValues(fct, values);
            bool fctValue = currentModel[fct];
            z3::expr_vector args = fctToArgs.at(fct);

            if (!fctValue) {
                // expect invalid placement ...
                if (fixedArgsCnt != board)
                    // we expect an invalid placement, but not all queen positions have been placed yet
                    return;
                std::vector<z3::expr_vector> conflicts;
                for (unsigned i = 0; i < args.size(); i++) {
                    if (values[i] != (unsigned)-1)
                        checkValidPlacement(conflicts, expr, args, values, i);
                }

                if (conflicts.empty()) {
                    // ... but we got a valid one
                    z3::expr_vector conflicting(ctx());
                    conflicting.push_back(fct);
                    for (const z3::expr &arg: args) {
                        if (!arg.is_numeral())
                            conflicting.push_back(arg);
                    }
                    this->conflict(conflicting);
                }
                else {
                    // ... and everything is fine; we have at least one conflict
                }
            }
            else {
                // expect valid placement ...
                std::vector<z3::expr_vector> conflicts;
                if (fixedFct){
                    for (unsigned i = 0; i < args.size(); i++) {
                        if (values[i] != (unsigned)-1) // check all set queens
                            checkValidPlacement(conflicts, expr, args, values, i);
                    }
                }
                else {
                    for (unsigned i = 0; i < args.size(); i++) {
                        if (z3::eq(args[i], expr)) // only check newly fixed values
                            checkValidPlacement(conflicts, fct, args, values, i);
                    }
                }
                if (conflicts.size() > 0) {
                    // ... but we got an invalid one
                    for (const z3::expr_vector &conflicting: conflicts)
                        this->conflict(conflicting);
                }
                else {
                    // ... and everything is fine; no conflict
                }
            }
        }
    }

//    void fixed(const z3::expr &expr, const z3::expr &value) override {
//        WriteLine("Fixed (" + to_string(nesting) + ") " + expr.to_string() + " to " + value.to_string());
//        unsigned v = value.is_true() ? 1 : (value.is_false() ? 0 : value.get_numeral_uint());
//        currentModel[expr] = v;
//        fixedValues.push_back(expr);
//
//        if (fctToArgs.contains(expr)) {
//            // fixed the value of a function
//
//            std::vector<unsigned> values;
//            unsigned fixedArgsCnt = getValues(expr, values);
//
//            if (!v && fixedArgsCnt != board)
//                // we expect an invalid placement, but not all queen positions have been placed yet
//                return;
//
//            z3::expr_vector args = fctToArgs.at(expr);
//
//            std::vector<z3::expr_vector> conflicts;
//            for (unsigned i = 0; i < args.size(); i++) {
//                if (values[i] != (unsigned)-1)
//                    checkValidPlacement(conflicts, expr, args, values, i);
//            }
//            if (v) {
//                //we expected a valid queen placement
//                if (conflicts.size() > 0) {
//                    // ... but we got an invalid one
//                    for (const z3::expr_vector &conflicting: conflicts)
//                        this->conflict(conflicting);
//                }
//                else {
//                    // everything fine; no conflict
//                }
//            }
//            else {
//                // we expect an invalid queen placement
//                if (conflicts.empty()) {
//                    // ... but we got a valid one
//                    z3::expr_vector conflicting(ctx());
//                    conflicting.push_back(expr);
//                    for (const z3::expr &arg: args) {
//                        if (!arg.is_numeral())
//                            conflicting.push_back(arg);
//                    }
//                    this->conflict(conflicting);
//                }
//                else {
//                    // everything fine; we have at least one conflict
//                }
//            }
//        }
//        else {
//            // fixed the value of a function argument
//
//            z3::expr_vector effectedFcts = argToFcts.at(expr);
//
//            for (const z3::expr& fct : effectedFcts) {
//                if (!currentModel.contains(fct))
//                    // we do not know yet whether to expect a valid or invalid placement
//                    continue;
//
//                std::vector<unsigned> values;
//                unsigned fixedArgsCnt = getValues(fct, values);
//                bool fctValue = currentModel[fct];
//                z3::expr_vector args = fctToArgs.at(fct);
//
//                if (!fctValue) {
//                    // expect invalid placement
//                    if (fixedArgsCnt != board)
//                        // we expect an invalid placement, but not all queen positions have been placed yet
//                        return;
//                    std::vector<z3::expr_vector> conflicts;
//                    for (unsigned i = 0; i < args.size(); i++) {
//                        if (values[i] != (unsigned)-1)
//                            checkValidPlacement(conflicts, expr, args, values, i);
//                    }
//
//                    if (conflicts.empty()) {
//                        // ... but we got a valid one
//                        z3::expr_vector conflicting(ctx());
//                        conflicting.push_back(fct);
//                        for (const z3::expr &arg: args) {
//                            if (!arg.is_numeral())
//                                conflicting.push_back(arg);
//                        }
//                        this->conflict(conflicting);
//                    }
//                    else {
//                        // everything fine; we have at least one conflict
//                    }
//                }
//                else {
//                    // expect valid placement
//                    std::vector<z3::expr_vector> conflicts;
//                    for (unsigned i = 0; i < args.size(); i++) {
//                        if (z3::eq(args[i], expr)) // only check newly fixed values
//                            checkValidPlacement(conflicts, fct, args, values, i);
//                    }
//                    if (conflicts.size() > 0) {
//                        // ... but we got an invalid one
//                        for (const z3::expr_vector &conflicting: conflicts)
//                            this->conflict(conflicting);
//                    }
//                    else {
//                        // everything fine; no conflict
//                    }
//                }
//            }
//        }
//    }

    void created(const z3::expr &func) override {
        WriteLine("Created (" + to_string(nesting) + "): " + func.to_string());
        z3::expr_vector args = func.args();
        for (unsigned i = 0; i < args.size(); i++) {
            z3::expr arg = args[i];

            if (!arg.is_numeral()) {
                WriteLine("Registered " + arg.to_string());
                this->add(arg);
            }
            else {
                currentModel[arg] = arg.get_numeral_uint();
                // Skip registering as argument is a fixed BV;
            }

            argToFcts.try_emplace(arg, ctx()).first->second.push_back(func);
        }
        fctToArgs.emplace(std::make_pair(func, args));
    }
};