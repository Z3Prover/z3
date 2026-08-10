/*++
Copyright (c) 2024 Microsoft Corporation

Module Name:

    lp_dio.cpp

Abstract:

    Tests for the Diophantine equation handling in the integer solver.

Author:

    Lev Nachmanson (levnach)

Revision History:

--*/
#include <iostream>
#include <utility>

#include "math/lp/int_solver.h"
#include "math/lp/lar_solver.h"
#include "util/rational.h"

namespace lp {
void test_dio() {
    std::cout << "test dio\n";
    lar_solver solver;
    int_solver i_solver(solver);
    lp::explanation exp;
    i_solver.set_expl(&exp);
    unsigned _x1 = 0;
    unsigned _x2 = 1;
    unsigned _x3 = 2;
    unsigned _fx_7 = 3;
    unsigned _fx_17 = 4;
    /*
        3x1 + 3x2 + 14x3 − 7 = 0
        7x1 + 12x2 + 31x3 − 17 = 0
    */
    lpvar x1 = solver.add_var(_x1, true);
    lpvar x2 = solver.add_var(_x2, true);
    lpvar x3 = solver.add_var(_x3, true);
    lpvar fx_7 = solver.add_var(_fx_7, true);
    lpvar fx_17 = solver.add_var(_fx_17, true);
    vector<std::pair<mpq, lpvar>> term_ls;
    /* 3x1 + 3x2 + 14x3 − 7 */
    term_ls.push_back(std::pair<mpq, lpvar>(mpq(3), x1));
    term_ls.push_back(std::pair<mpq, lpvar>(mpq(3), x2));
    term_ls.push_back(std::pair<mpq, lpvar>(mpq(14), x3));
    term_ls.push_back(std::pair<mpq, lpvar>(mpq(-1), fx_7));
    for (auto & p: term_ls) {
        p.first = -p.first;
    }
    unsigned t0 = solver.add_term(term_ls, 10);
    term_ls.clear();
    /* 7x1 + 12x2 + 31x3 − 17 = 0*/
    term_ls.push_back(std::pair<mpq, lpvar>(mpq(7), x1));
    term_ls.push_back(std::pair<mpq, lpvar>(mpq(12), x2));
    term_ls.push_back(std::pair<mpq, lpvar>(mpq(31), x3));
    term_ls.push_back(std::pair<mpq, lpvar>(mpq(-1), fx_17));

    for (auto & p: term_ls) {
        p.first = -p.first;
    }
    solver.add_var_bound(fx_7, LE, mpq(-7));
    solver.add_var_bound(fx_7, GE, mpq(-7));
    solver.add_var_bound(t0, LE, mpq(0));
    solver.add_var_bound(t0, GE, mpq(0));
    solver.find_feasible_solution();
    ENSURE(solver.get_status() == lp_status::OPTIMAL);
#ifdef Z3DEBUG
    i_solver.dio_test();
#endif

    solver.push();
    unsigned t1 = solver.add_term(term_ls, 11);
    solver.add_var_bound(fx_17, LE, mpq(-17));
    solver.add_var_bound(fx_17, GE, mpq(-17));
    solver.add_var_bound(t1, LE, mpq(0));
    solver.add_var_bound(t1, GE, mpq(0));
    solver.find_feasible_solution();
    ENSURE(solver.get_status() == lp_status::OPTIMAL);
#ifdef Z3DEBUG
    i_solver.dio_test();
#endif

    solver.pop();
    solver.find_feasible_solution();
    ENSURE(solver.get_status() == lp_status::OPTIMAL);
#ifdef Z3DEBUG
    i_solver.dio_test();
#endif
}
}  // namespace lp

void tst_lp_dio() {
    lp::test_dio();
}
