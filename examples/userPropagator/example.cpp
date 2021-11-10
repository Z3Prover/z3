#include <algorithm>
#include <chrono>
#include <iostream>
#include <random>
#include <stack>
#include <unordered_map>
#include <unordered_set>
#include <vector>
#include <cstring>
#include "z3++.h"

/**
 * The program solves the n-queens problem (number of solutions) with 4 different approaches
 * 1) Bit-Vector constraints + Default solver + Blocking Clauses
 * 2) Bit-Vector constraints + Simple solver + Blocking Clauses
 * 3) Bit-Vector constraints + Simple solver + Adding contradictions in the propagator
 * 4) Constraints only implicit via the propagator + Simple solver + Adding contradictions in the propagator
 *
 * Runs 1 + 2 are done for comparison with 3 + 4
 */

using namespace std::chrono;
using std::to_string;

#define QUEEN
#define REPETITIONS 5

#define SIZE(x) std::extent<decltype(x)>::value

#ifdef LOG
#define WriteEmptyLine std::cout << std::endl
#define WriteLine(x) std::cout << (x) << std::endl
#define Write(x) std::cout << x
#else
#define WriteEmptyLine
#define WriteLine(x)
#define Write(x)
#endif

typedef std::vector<unsigned> model;

struct model_hash_function {
    std::size_t operator()(const model &m) const {
        size_t hash = 0;
        for (unsigned i = 0; i < m.size(); i++) {
            hash *= m.size();
            hash += m[i];
        }
        return hash;
    }
};

class user_propagator : public z3::user_propagator_base {

protected:

    unsigned board;
    std::unordered_map<unsigned, unsigned>& id_mapping;
    model currentModel;
    std::unordered_set<model, model_hash_function> modelSet;
    std::vector<unsigned> fixedValues;
    std::stack<unsigned> fixedCnt;

    int solutionId = 1;

public:

    int getModelCount() const {
        return solutionId - 1;
    }

    void final() final {
        this->conflict((unsigned) fixedValues.size(), fixedValues.data());
        if (modelSet.find(currentModel) != modelSet.end()) {
            WriteLine("Got already computed model");
            return;
        }
        Write("Model #" << solutionId << ":\n");
        solutionId++;
#ifdef LOG
        for (unsigned i = 0; i < fixedValues.size(); i++) {
            unsigned id = fixedValues[i];
            WriteLine("q" + to_string(id_mapping[id]) + " = " + to_string(currentModel[id]));
        }
#endif
        modelSet.insert(currentModel);
        WriteEmptyLine;
    }

    static unsigned bvToInt(z3::expr e) {
        return (unsigned)e.get_numeral_int();
    }

    void fixed(unsigned id, z3::expr const &e) override {
        fixedValues.push_back(id);
        unsigned value = bvToInt(e);
        currentModel[id_mapping[id]] = value;
    }

    user_propagator(z3::solver *s, std::unordered_map<unsigned, unsigned>& idMapping, unsigned board)
            : user_propagator_base(s), board(board), id_mapping(idMapping), currentModel(board, (unsigned)-1) {

        this->register_fixed();
        this->register_final();
    }

    virtual ~user_propagator() = default;

    void push() override {
        fixedCnt.push((unsigned) fixedValues.size());
    }

    void pop(unsigned num_scopes) override {
        for (unsigned i = 0; i < num_scopes; i++) {
            unsigned lastCnt = fixedCnt.top();
            fixedCnt.pop();
            for (auto j = fixedValues.size(); j > lastCnt; j--) {
                currentModel[fixedValues[j - 1]] = (unsigned)-1;
            }
            fixedValues.resize(lastCnt);
        }
    }

    user_propagator_base *fresh(Z3_context) override { return this; }
};

class user_propagator_with_theory : public user_propagator {

public:

    void fixed(unsigned id, z3::expr const &e) override {
        unsigned queenId = id_mapping[id];
        unsigned queenPos = bvToInt(e);

        if (queenPos >= board) {
            this->conflict(1, &id);
            return;
        }

        for (unsigned fixed : fixedValues) {
            unsigned otherId = id_mapping[fixed];
            unsigned otherPos = currentModel[fixed];

            if (queenPos == otherPos) {
                const unsigned conflicting[] = {id, fixed};
                this->conflict(2, conflicting);
                continue;
            }
#ifdef QUEEN
            int diffY = abs((int)queenId - (int)otherId);
            int diffX = abs((int)queenPos - (int)otherPos);
            if (diffX == diffY) {
                const unsigned conflicting[] = {id, fixed};
                this->conflict(2, conflicting);
            }
#endif
        }

        fixedValues.push_back(id);
        currentModel[id_mapping[id]] = queenPos;
    }

    user_propagator_with_theory(z3::solver *s, std::unordered_map<unsigned, unsigned>& idMapping, unsigned board)
            : user_propagator(s, idMapping, board) {}
};

int log2i(unsigned n) {
    if (n <= 0) {
        return 0;
    }
    if (n <= 2) {
        return 1;
    }
    unsigned l = 1;
    int i = 0;
    while (l < n) {
        l <<= 1;
        i++;
    }
    return i;
}

std::vector<z3::expr> createQueens(z3::context &context, unsigned num) {
    std::vector<z3::expr> queens;
    int bits = log2i(num) + 1 /*to detect potential overflow in the diagonal*/;
    for (unsigned i = 0; i < num; i++) {
        queens.push_back(context.bv_const((std::string("q") + to_string(i)).c_str(), bits));
    }
    return queens;
}

void createConstraints(z3::context &context, z3::solver &solver, const std::vector<z3::expr> &queens) {
    for (unsigned i = 0; i < queens.size(); i++) {
        // assert column range
        solver.add(z3::uge(queens[i], 0));
        solver.add(z3::ule(queens[i], (int) (queens.size() - 1)));
    }

    z3::expr_vector distinct(context);
    for (const z3::expr &queen : queens) {
        distinct.push_back(queen);
    }

    solver.add(z3::distinct(distinct));

#ifdef QUEEN
    for (unsigned i = 0; i < queens.size(); i++) {
        for (unsigned j = i + 1; j < queens.size(); j++) {
            solver.add((int)(j - i) != (queens[j] - queens[i]));
            solver.add((int)(j - i) != (queens[i] - queens[j]));
        }
    }
#endif
}

int test01(unsigned num, bool simple) {
    z3::context context;
    z3::solver solver(context, !simple ? Z3_mk_solver(context) : Z3_mk_simple_solver(context));

    std::vector<z3::expr> queens = createQueens(context, num);

    createConstraints(context, solver, queens);

    int solutionId = 1;

    while (true) {
        z3::check_result res = solver.check();

        if (res != z3::check_result::sat) {
            break;
        }

        z3::model model = solver.get_model();

        WriteLine("Model #" + to_string(solutionId) + ":");
        solutionId++;

        z3::expr_vector blocking(context);

        for (unsigned i = 0; i < num; i++) {
            z3::expr eval = model.eval(queens[i]);
            WriteLine(("q" + to_string(i) + " = " + to_string(eval.get_numeral_int())));
            blocking.push_back(queens[i] != eval);
        }

        solver.add(z3::mk_or(blocking));

        WriteEmptyLine;
    }
    return solutionId - 1;
}

inline int test0(unsigned num) {
    return test01(num, false);
}

inline int test1(unsigned num) {
    return test01(num, true);
}

int test23(unsigned num, bool withTheory) {
    z3::context context;
    z3::solver solver(context, Z3_mk_simple_solver(context));
    std::unordered_map<unsigned, unsigned> idMapping;

    user_propagator *propagator;
    if (!withTheory) {
        propagator = new user_propagator(&solver, idMapping, num);
    }
    else {
        propagator = new user_propagator_with_theory(&solver, idMapping, num);
    }

    std::vector<z3::expr> queens = createQueens(context, num);

    for (unsigned i = 0; i < queens.size(); i++) {
        unsigned id = propagator->add(queens[i]);
        idMapping[id] = i;
    }

    if (!withTheory) {
        createConstraints(context, solver, queens);
    }

    solver.check();
    int res = propagator->getModelCount();
    delete propagator;
    return res;
}

inline int test2(unsigned num) {
    return test23(num, false);
}

inline int test3(unsigned num) {
    return test23(num, true);
}

int main() {

    for (int num = 4; num <= 11; num++) {

        std::cout << "num = " << num << ":\n" << std::endl;

        unsigned seed = (unsigned) high_resolution_clock::now().time_since_epoch().count();
        const char *testName[] =
                {
                        "BV + Blocking clauses (Default solver)",
                        "BV + Blocking clauses (Simple solver)",
                        "BV + Adding conflicts",
                        "Custom theory + conflicts",
                };
        int permutation[4] =
                {
                        0,
                        1,
                        2,
                        3,
                };
        double timeResults[REPETITIONS * SIZE(permutation)];

        for (int rep = 0; rep < REPETITIONS; rep++) {
            // Execute strategies in a randomised order
            std::shuffle(&permutation[0], &permutation[SIZE(permutation) - 1], std::default_random_engine(seed));

            for (int i : permutation) {
                int modelCount = -1;

                auto now1 = high_resolution_clock::now();

                switch (i) {
                    case 0:
                        modelCount = test0(num);
                        break;
                    case 1:
                        modelCount = test1(num);
                        break;
                    case 2:
                        modelCount = test2(num);
                        break;
                    case 3:
                        modelCount = test3(num);
                        break;
                    default:
                        WriteLine("Unknown case");
                        break;
                }
                auto now2 = high_resolution_clock::now();
                duration<double, std::milli> ms = now2 - now1;
                std::cout << testName[i] << " took " << ms.count() << "ms (" << modelCount << " models)" << std::endl;
                timeResults[rep * SIZE(permutation) + i] = ms.count();
                WriteLine("-------------");
            }
        }

        std::cout << "\n" << std::endl;

        for (unsigned i = 0; i < SIZE(permutation); i++) {
            std::cout << testName[i];
            double sum = 0;
            for (int j = 0; j < REPETITIONS; j++) {
                std::cout << " " << timeResults[j * SIZE(permutation) + i] << "ms";
                sum += timeResults[j * SIZE(permutation) + i];
            }
            std::cout << " | avg: " << sum / REPETITIONS << "ms" << std::endl;
        }

        std::cout << std::endl;
    }
}
