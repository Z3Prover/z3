/*++
  Copyright (c) 2020 Microsoft Corporation

  Module Name:

  lcube.cpp

  Abstract:

  Tests for the largest cube test of Bromberger and Weidenbach
  (Fast Cube Tests for LIA Constraint Solving, IJCAR 2016),
  implemented in int_cube::find_largest_cube().

  This file lives directly under src/test (not src/test/lp) so that the
  scripts/mk_make.py build, which only compiles the top-level test
  directory, links tst_lcube().

  Author:

  Lev Nachmanson (levnach)

  --*/

#include <initializer_list>
#include <iostream>
#include <utility>

#include "util/debug.h"
#include "util/params.h"
#include "math/lp/int_cube.h"
#include "math/lp/int_solver.h"
#include "math/lp/lar_solver.h"
#include "math/lp/numeric_pair.h"

namespace lp {

// tests for the largest cube test of Bromberger and Weidenbach
namespace lcube_test {

    struct ineq {
        vector<std::pair<mpq, unsigned>> m_coeffs;
        lconstraint_kind m_kind;
        mpq m_rs;
    };

    // builds for every inequality a term with the bound and solves
    static void setup(lar_solver& solver, const vector<ineq>& ineqs, svector<unsigned>* term_columns = nullptr) {
        unsigned term_ext = 1000;
        for (const auto& in : ineqs) {
            unsigned t = solver.add_term(in.m_coeffs, term_ext++);
            solver.add_var_bound(t, in.m_kind, in.m_rs);
            if (term_columns)
                term_columns->push_back(t);
        }
        auto st = solver.solve();
        VERIFY(st == lp_status::OPTIMAL || st == lp_status::FEASIBLE);
    }

    static void verify_model(const lar_solver& solver, const vector<ineq>& ineqs) {
        for (const auto& in : ineqs) {
            impq v;
            for (const auto& p : in.m_coeffs)
                v += solver.get_column_value(p.second) * p.first;
            switch (in.m_kind) {
            case lconstraint_kind::LE: VERIFY(v <= impq(in.m_rs)); break;
            case lconstraint_kind::GE: VERIFY(v >= impq(in.m_rs)); break;
            default: VERIFY(false);
            }
        }
    }

    static void verify_int_values(const lar_solver& solver, std::initializer_list<unsigned> vars) {
        for (unsigned j : vars)
            VERIFY(solver.get_column_value(j).is_int());
    }

    // The example of Bromberger and Weidenbach: 3x1 - x2 <= 0, -2x1 - x2 <= -2, -2x1 + x2 <= 1.
    // The largest cube is smaller than the unit cube, the rounded center is not a solution,
    // no coordinate flip repairs it (the only integer solution lies outside the lattice cell
    // of the center): expect undef and an intact solver state.
    static void test_paper_example_undef() {
        std::cout << "lcube: paper example, expecting undef\n";
        lar_solver solver;
        unsigned x1 = solver.add_named_var(0, true, "x1");
        unsigned x2 = solver.add_named_var(1, true, "x2");
        vector<ineq> ineqs;
        ineqs.push_back(ineq{{{mpq(3), x1}, {mpq(-1), x2}}, lconstraint_kind::LE, mpq(0)});
        ineqs.push_back(ineq{{{mpq(-2), x1}, {mpq(-1), x2}}, lconstraint_kind::LE, mpq(-2)});
        ineqs.push_back(ineq{{{mpq(-2), x1}, {mpq(1), x2}}, lconstraint_kind::LE, mpq(1)});
        setup(solver, ineqs);
        int_solver i_s(solver);
        solver.set_int_solver(&i_s);
        lia_move m = int_cube(i_s).find_largest_cube();
        std::cout << "lcube returned " << lia_move_to_string(m) << "\n";
        VERIFY(m == lia_move::undef);
        VERIFY(solver.ax_is_correct());
    }

    // 3x1 - x2 <= 0, -2x1 - x2 <= -1, -2x1 + x2 <= 1: the largest cube has
    // edge 4/17 with the center (3/17, 1) that rounds to the solution (0, 1),
    // while the unit cube test fails: the largest cube test is stronger here.
    static void test_beats_unit_cube() {
        std::cout << "lcube: beating the unit cube test\n";
        lar_solver solver;
        unsigned x1 = solver.add_named_var(0, true, "x1");
        unsigned x2 = solver.add_named_var(1, true, "x2");
        vector<ineq> ineqs;
        ineqs.push_back(ineq{{{mpq(3), x1}, {mpq(-1), x2}}, lconstraint_kind::LE, mpq(0)});
        ineqs.push_back(ineq{{{mpq(-2), x1}, {mpq(-1), x2}}, lconstraint_kind::LE, mpq(-1)});
        ineqs.push_back(ineq{{{mpq(-2), x1}, {mpq(1), x2}}, lconstraint_kind::LE, mpq(1)});
        svector<unsigned> tcols;
        setup(solver, ineqs, &tcols);
        // move the solution to a fractional feasible point: the cube tests only
        // run when the current solution has fractional integer variables
        solver.set_column_value_test(x1, impq(mpq(1, 4)));
        solver.set_column_value_test(x2, impq(mpq(5, 4)));
        solver.set_column_value_test(tcols[0], impq(mpq(-1, 2)));
        solver.set_column_value_test(tcols[1], impq(mpq(-7, 4)));
        solver.set_column_value_test(tcols[2], impq(mpq(3, 4)));
        int_solver i_s(solver);
        solver.set_int_solver(&i_s);
        lia_move m = int_cube(i_s)();
        std::cout << "unit cube returned " << lia_move_to_string(m) << "\n";
        VERIFY(m == lia_move::undef);
        m = int_cube(i_s).find_largest_cube();
        std::cout << "lcube returned " << lia_move_to_string(m) << "\n";
        VERIFY(m == lia_move::sat);
        verify_int_values(solver, {x1, x2});
        verify_model(solver, ineqs);
    }

    // 9/10 <= x + y + r <= 11/10, -11/10 <= x - y + r <= 1/10, 0 <= r <= 1/10,
    // x, y integer, r real. The real variable keeps the terms and their bounds
    // non-integer. A fractional center, e.g. (1/2, 1/2), rounds to an infeasible
    // point that is repaired by flipping one coordinate: expect sat.
    static void test_flip_repair() {
        std::cout << "lcube: rounding repair\n";
        lar_solver solver;
        unsigned x = solver.add_named_var(0, true, "x");
        unsigned y = solver.add_named_var(1, true, "y");
        unsigned r = solver.add_named_var(2, false, "r");
        solver.add_var_bound(r, lconstraint_kind::GE, mpq(0));
        solver.add_var_bound(r, lconstraint_kind::LE, mpq(1, 10));
        vector<ineq> ineqs;
        ineqs.push_back(ineq{{{mpq(1), x}, {mpq(1), y}, {mpq(1), r}}, lconstraint_kind::GE, mpq(9, 10)});
        ineqs.push_back(ineq{{{mpq(1), x}, {mpq(1), y}, {mpq(1), r}}, lconstraint_kind::LE, mpq(11, 10)});
        ineqs.push_back(ineq{{{mpq(1), x}, {mpq(-1), y}, {mpq(1), r}}, lconstraint_kind::GE, mpq(-11, 10)});
        ineqs.push_back(ineq{{{mpq(1), x}, {mpq(-1), y}, {mpq(1), r}}, lconstraint_kind::LE, mpq(1, 10)});
        setup(solver, ineqs);
        int_solver i_s(solver);
        solver.set_int_solver(&i_s);
        lia_move m = int_cube(i_s).find_largest_cube();
        std::cout << "lcube returned " << lia_move_to_string(m)
                  << ", flip successes: " << solver.settings().stats().m_lcube_flip_success << "\n";
        VERIFY(m == lia_move::sat);
        verify_int_values(solver, {x, y});
        verify_model(solver, ineqs);
    }

    // 3x + 5y >= 7 alone has infinite lattice width: the edge length is
    // unbounded and any cube center of edge >= 1 rounds to a solution.
    static void test_infinite_lattice_width() {
        std::cout << "lcube: infinite lattice width\n";
        lar_solver solver;
        unsigned x = solver.add_named_var(0, true, "x");
        unsigned y = solver.add_named_var(1, true, "y");
        vector<ineq> ineqs;
        ineqs.push_back(ineq{{{mpq(3), x}, {mpq(5), y}}, lconstraint_kind::GE, mpq(7)});
        setup(solver, ineqs);
        int_solver i_s(solver);
        solver.set_int_solver(&i_s);
        lia_move m = int_cube(i_s).find_largest_cube();
        std::cout << "lcube returned " << lia_move_to_string(m) << "\n";
        VERIFY(m == lia_move::sat);
        verify_int_values(solver, {x, y});
        verify_model(solver, ineqs);
    }

    // 0 <= x + 2y + r <= 8, 0 <= x - 2y + r <= 8: the maximal edge length is
    // 8/3 >= 1, so the rounded center is guaranteed to be a solution.
    static void test_edge_at_least_one() {
        std::cout << "lcube: edge length at least 1\n";
        lar_solver solver;
        unsigned x = solver.add_named_var(0, true, "x");
        unsigned y = solver.add_named_var(1, true, "y");
        unsigned r = solver.add_named_var(2, false, "r");
        solver.add_var_bound(r, lconstraint_kind::GE, mpq(0));
        solver.add_var_bound(r, lconstraint_kind::LE, mpq(1, 10));
        vector<ineq> ineqs;
        ineqs.push_back(ineq{{{mpq(1), x}, {mpq(2), y}, {mpq(1), r}}, lconstraint_kind::GE, mpq(0)});
        ineqs.push_back(ineq{{{mpq(1), x}, {mpq(2), y}, {mpq(1), r}}, lconstraint_kind::LE, mpq(8)});
        ineqs.push_back(ineq{{{mpq(1), x}, {mpq(-2), y}, {mpq(1), r}}, lconstraint_kind::GE, mpq(0)});
        ineqs.push_back(ineq{{{mpq(1), x}, {mpq(-2), y}, {mpq(1), r}}, lconstraint_kind::LE, mpq(8)});
        setup(solver, ineqs);
        int_solver i_s(solver);
        solver.set_int_solver(&i_s);
        lia_move m = int_cube(i_s).find_largest_cube();
        std::cout << "lcube returned " << lia_move_to_string(m) << "\n";
        VERIFY(m == lia_move::sat);
        verify_int_values(solver, {x, y});
        verify_model(solver, ineqs);
    }

    // runs the flip-repair instance through int_solver::check() with the
    // lp.lcube parameter set and the cube period lowered to 1: verifies the
    // dispatch and the parameter plumbing
    static void test_dispatch() {
        std::cout << "lcube: dispatch through int_solver::check\n";
        lar_solver solver;
        params_ref p;
        p.set_bool("lcube", true);
        solver.settings().updt_params(p);
        VERIFY(solver.settings().lcube());
        solver.settings().m_int_find_cube_period = 1;
        unsigned x = solver.add_named_var(0, true, "x");
        unsigned y = solver.add_named_var(1, true, "y");
        unsigned r = solver.add_named_var(2, false, "r");
        solver.add_var_bound(r, lconstraint_kind::GE, mpq(0));
        solver.add_var_bound(r, lconstraint_kind::LE, mpq(1, 10));
        vector<ineq> ineqs;
        ineqs.push_back(ineq{{{mpq(1), x}, {mpq(1), y}, {mpq(1), r}}, lconstraint_kind::GE, mpq(9, 10)});
        ineqs.push_back(ineq{{{mpq(1), x}, {mpq(1), y}, {mpq(1), r}}, lconstraint_kind::LE, mpq(11, 10)});
        ineqs.push_back(ineq{{{mpq(1), x}, {mpq(-1), y}, {mpq(1), r}}, lconstraint_kind::GE, mpq(-11, 10)});
        ineqs.push_back(ineq{{{mpq(1), x}, {mpq(-1), y}, {mpq(1), r}}, lconstraint_kind::LE, mpq(1, 10)});
        svector<unsigned> tcols;
        setup(solver, ineqs, &tcols);
        // a fractional feasible point, so that check() does not return sat right away
        solver.set_column_value_test(x, impq(mpq(1, 2)));
        solver.set_column_value_test(y, impq(mpq(1, 2)));
        solver.set_column_value_test(r, impq(mpq(1, 10)));
        solver.set_column_value_test(tcols[0], impq(mpq(11, 10)));
        solver.set_column_value_test(tcols[1], impq(mpq(11, 10)));
        solver.set_column_value_test(tcols[2], impq(mpq(1, 10)));
        solver.set_column_value_test(tcols[3], impq(mpq(1, 10)));
        int_solver i_s(solver);
        solver.set_int_solver(&i_s);
        explanation ex;
        lia_move m = i_s.check(&ex);
        std::cout << "check returned " << lia_move_to_string(m)
                  << ", lcube calls: " << solver.settings().stats().m_lcube_calls << "\n";
        VERIFY(m == lia_move::sat);
        VERIFY(solver.settings().stats().m_lcube_calls >= 1);
        verify_int_values(solver, {x, y});
        verify_model(solver, ineqs);
    }

    static void run() {
        test_paper_example_undef();
        test_beats_unit_cube();
        test_flip_repair();
        test_infinite_lattice_width();
        test_edge_at_least_one();
        test_dispatch();
        std::cout << "lcube tests passed\n";
    }
} // namespace lcube_test
}  // namespace lp

void tst_lcube() {
    lp::lcube_test::run();
}
