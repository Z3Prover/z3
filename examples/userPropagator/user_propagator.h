#pragma once

#include "common.h"

class user_propagator : public z3::user_propagator_base {

protected:

    unsigned board;
    std::unordered_map<z3::expr, unsigned> &queenToY;
    simple_model currentModel;
    std::unordered_set<simple_model> modelSet;
    z3::expr_vector fixedValues;
    std::stack<unsigned> fixedCnt;

    int solutionNr = 1;

public:

    int getModelCount() const {
        return solutionNr - 1;
    }

    void final() override {
        this->conflict(fixedValues);
        if (modelSet.find(currentModel) != modelSet.end()) {
            WriteLine("Got already computed model");
            return;
        }
        Write("Model #" << solutionNr << ":\n");
        solutionNr++;
#ifdef VERBOSE
        for (unsigned i = 0; i < fixedValues.size(); i++) {
            z3::expr fixed = fixedValues[i];
            WriteLine("q" + to_string(queenToY[fixed]) + " = " + to_string(currentModel[queenToY[fixed]]));
        }
#endif
        modelSet.insert(currentModel);
        WriteEmptyLine;
    }

    static unsigned bvToInt(z3::expr const &e) {
        return (unsigned) e.get_numeral_int();
    }

    void fixed(z3::expr const &ast, z3::expr const &value) override {
        fixedValues.push_back(ast);
        unsigned valueBv = bvToInt(value);
        currentModel[queenToY[ast]] = valueBv;
    }

    user_propagator(z3::context &c, std::unordered_map<z3::expr, unsigned> &queenToY, unsigned board)
            : user_propagator_base(c), board(board), queenToY(queenToY), fixedValues(c), currentModel(board, (unsigned) -1) {

        this->register_fixed();
        this->register_final();
    }

    user_propagator(z3::solver *s, std::unordered_map<z3::expr, unsigned> &idMapping, unsigned board)
            : user_propagator_base(s), board(board), queenToY(idMapping), fixedValues(s->ctx()), currentModel(board, (unsigned) -1) {

        this->register_fixed();
        this->register_final();
    }

    ~user_propagator() = default;

    void push() override {
        fixedCnt.push((unsigned) fixedValues.size());
    }

    void pop(unsigned num_scopes) override {
        for (unsigned i = 0; i < num_scopes; i++) {
            unsigned lastCnt = fixedCnt.top();
            fixedCnt.pop();
            // Remove fixed values from model
            for (unsigned j = fixedValues.size(); j > lastCnt; j--) {
                currentModel[queenToY[fixedValues[j - 1]]] = (unsigned) -1;
            }
            fixedValues.resize(lastCnt);
        }
    }

    user_propagator_base *fresh(z3::context &) override {
        return this;
    }
};