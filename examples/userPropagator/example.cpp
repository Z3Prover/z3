#include "user_propagator.h"
#include "user_propagator_with_theory.h"
#include "user_propagator_subquery_maximisation.h"
#include "user_propagator_internal_maximisation.h"
#include "user_propagator_created_maximisation.h"

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

#define REPETITIONS 5

#define MIN_BOARD 4
#define MAX_BOARD1 12
#define MAX_BOARD2 12

z3::expr_vector createQueens(z3::context &context, unsigned num, int bits, std::string prefix) {
    z3::expr_vector queens(context);
    for (unsigned i = 0; i < num; i++) {
        queens.push_back(context.bv_const((prefix + "q" + to_string(i)).c_str(), bits));
    }
    return queens;
}

z3::expr_vector createQueens(z3::context &context, unsigned num) {
    return createQueens(context, num, log2i(num) + 1, "");
}

z3::expr createConstraints(z3::context &context, const z3::expr_vector &queens) {
    z3::expr_vector assertions(context);
    for (unsigned i = 0; i < queens.size(); i++) {
        // assert column range
        assertions.push_back(z3::uge(queens[i], 0));
        assertions.push_back(z3::ule(queens[i], (int) (queens.size() - 1)));
    }

    z3::expr_vector distinct(context);
    for (const z3::expr &queen: queens) {
        distinct.push_back(queen);
    }

    assertions.push_back(z3::distinct(distinct));

    for (unsigned i = 0; i < queens.size(); i++) {
        for (unsigned j = i + 1; j < queens.size(); j++) {
            assertions.push_back((int) (j - i) != (queens[j] - queens[i]));
            assertions.push_back((int) (j - i) != (queens[i] - queens[j]));
        }
    }

    return z3::mk_and(assertions);
}

int test01(unsigned num, bool simple) {
    z3::context context;
    z3::solver solver(context, !simple ? Z3_mk_solver(context) : Z3_mk_simple_solver(context));

    z3::expr_vector queens = createQueens(context, num);

    solver.add(createConstraints(context, queens));

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
    z3::solver solver(context, z3::solver::simple());
    std::unordered_map<z3::expr, unsigned> idMapping;

    user_propagator *propagator;
    if (!withTheory) {
        propagator = new user_propagator(&solver, idMapping, num);
    }
    else {
        propagator = new user_propagator_with_theory(&solver, idMapping, num);
    }

    z3::expr_vector queens = createQueens(context, num);

    for (unsigned i = 0; i < queens.size(); i++) {
        propagator->add(queens[i]);
        idMapping[queens[i]] = i;
    }

    if (!withTheory) {
        solver.add(createConstraints(context, queens));
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

int test4(unsigned num) {
    z3::context context;
    z3::solver solver(context, z3::solver::simple());

    z3::expr_vector queens1 = createQueens(context, num, log2i(num * num), ""); // square to avoid overflow during summation

    z3::expr valid1 = createConstraints(context, queens1);

    z3::expr_vector queens2 = createQueens(context, num, log2i(num * num), "forall_");

    z3::expr valid2 = createConstraints(context, queens2);

    z3::expr manhattanSum1 = context.bv_val(0, queens1[0].get_sort().bv_size());
    z3::expr manhattanSum2 = context.bv_val(0, queens2[0].get_sort().bv_size());

    for (int i = 1; i < queens1.size(); i++) {
        manhattanSum1 = manhattanSum1 + z3::ite(z3::uge(queens1[i], queens1[i - 1]), queens1[i] - queens1[i - 1], queens1[i - 1] - queens1[i]);
        manhattanSum2 = manhattanSum2 + z3::ite(z3::uge(queens2[i], queens2[i - 1]), queens2[i] - queens2[i - 1], queens2[i - 1] - queens2[i]);
    }


    solver.add(valid1 && z3::forall(queens2, z3::implies(valid2, manhattanSum1 >= manhattanSum2)));

    solver.check();
    z3::model model = solver.get_model();

    int max = 0;

    int prev, curr;
    curr = model.eval(queens1[0]).get_numeral_int();

    for (unsigned i = 1; i < num; i++) {
        prev = curr;
        curr = model.eval(queens1[i]).get_numeral_int();
        max += abs(curr - prev);
    }

    return max;
}

int test5(unsigned num) {
    z3::context context;
    z3::solver solver(context, z3::solver::simple());
    std::unordered_map<z3::expr, unsigned> idMapping;

    z3::expr_vector queens = createQueens(context, num, log2i(num * num), "");

    solver.add(createConstraints(context, queens));

    user_propagator_subquery_maximisation propagator(&solver, idMapping, num, queens);

    for (unsigned i = 0; i < queens.size(); i++) {
        propagator.add(queens[i]);
        idMapping[queens[i]] = i;
    }

    solver.check();
    z3::model model = solver.get_model();

    int max = 0;

    int prev, curr;
    curr = model.eval(queens[0]).get_numeral_int();
    for (unsigned i = 1; i < num; i++) {
        prev = curr;
        curr = model.eval(queens[i]).get_numeral_int();
        max += abs(curr - prev);
    }

    return max;
}

int test6(unsigned num) {
    z3::context context;
    z3::solver solver(context, z3::solver::simple());
    std::unordered_map<z3::expr, unsigned> idMapping;

    z3::expr_vector queens = createQueens(context, num, log2i(num * num), "");

    solver.add(createConstraints(context, queens));

    user_propagator_internal_maximisation propagator(&solver, idMapping, num, queens);

    for (unsigned i = 0; i < queens.size(); i++) {
        propagator.add(queens[i]);
        idMapping[queens[i]] = i;
    }

    solver.check();
    return propagator.best;
}

int test7(unsigned num) {
    z3::context context;
    z3::solver solver(context, z3::solver::simple());

    z3::expr_vector queens1 = createQueens(context, num, log2i(num * num), "");
    z3::expr_vector queens2 = createQueens(context, num, log2i(num * num), "forall_");

    z3::expr manhattanSum1 = context.bv_val(0, queens1[0].get_sort().bv_size());
    z3::expr manhattanSum2 = context.bv_val(0, queens2[0].get_sort().bv_size());

    for (int i = 1; i < queens1.size(); i++) {
        manhattanSum1 = manhattanSum1 + z3::ite(z3::uge(queens1[i], queens1[i - 1]), queens1[i] - queens1[i - 1], queens1[i - 1] - queens1[i]);
        manhattanSum2 = manhattanSum2 + z3::ite(z3::uge(queens2[i], queens2[i - 1]), queens2[i] - queens2[i - 1], queens2[i - 1] - queens2[i]);
    }

    z3::sort_vector domain(context);
    for (int i = 0; i < queens1.size(); i++) {
        domain.push_back(queens1[i].get_sort());
    }
    z3::func_decl validFunc = context.user_propagate_function(context.str_symbol("valid"), domain, context.bool_sort());

    solver.add(validFunc(queens1) && z3::forall(queens2, z3::implies(validFunc(queens2), manhattanSum1 >= manhattanSum2)));
    user_propagator_created_maximisation propagator(&solver, num);

    solver.check();
    z3::model model = solver.get_model();

    int max = 0;

    int prev, curr;
    curr = model.eval(queens1[0]).get_numeral_int();

    for (unsigned i = 1; i < num; i++) {
        prev = curr;
        curr = model.eval(queens1[i]).get_numeral_int();
        max += abs(curr - prev);
    }

    return max;
}

int main() {

    for (int num = MIN_BOARD; num <= MAX_BOARD1; num++) {

      std::cout << "num = " << num << ":\n" << std::endl;

      unsigned seed = (unsigned) high_resolution_clock::now().time_since_epoch().count();
      const char *testName[] =
              {
                      "BV + Blocking clauses (Default solver)",
                      "BV + Blocking clauses (Simple solver)",
                      "BV + Adding conflicts",
                      "Custom theory + conflicts",
              };
      int permutation[4] = {0, 1, 2, 3,};
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

    z3::set_param("smt.ematching", "false");
    z3::set_param("smt.mbqi", "true");

    std::cout << "\nMaximal distance:" << std::endl;

    for (int num = MIN_BOARD; num <= MAX_BOARD2; num++) {

        std::cout << "num = " << num << ":\n" << std::endl;

        unsigned seed = (unsigned) high_resolution_clock::now().time_since_epoch().count();
        const char *testName[] =
                {
                        "Ordinary/Direct Encoding",
                        "SubQuery in final",
                        "Assert Smaller in final",
                        "created",
                };
        int permutation[4] = {0, 1, 2, 3,};
        double timeResults[REPETITIONS * SIZE(permutation)];

        for (int rep = 0; rep < REPETITIONS; rep++) {
            // Execute strategies in a randomised order
            std::shuffle(&permutation[0], &permutation[SIZE(permutation) - 1], std::default_random_engine(seed));

            for (int i: permutation) {
                int max = -1;

                auto now1 = high_resolution_clock::now();

                switch (i + 4) {
                    case 4:
                        max = test4(num);
                        break;
                    case 5:
                        max = test5(num);
                        break;
                    case 6:
                        max = test6(num);
                        break;
                    case 7:
                        max = test7(num);
                        break;
                    default:
                        WriteLine("Unknown case");
                        break;
                }
                auto now2 = high_resolution_clock::now();
                duration<double, std::milli> ms = now2 - now1;
                std::cout << testName[i] << " took " << ms.count() << "ms. Max: " << max << std::endl;
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