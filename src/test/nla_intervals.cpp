/*++
Copyright (c) 2024 Microsoft Corporation

Module Name:

    nla_intervals.cpp

Abstract:

    Tests for NLA interval propagation functionality

Author:

    Test Coverage Improvement

Revision History:

--*/

#include "math/lp/nla_intervals.h"
#include "math/lp/nla_core.h"
#include "math/lp/lar_solver.h"
#include "util/rational.h"
#include "util/rlimit.h"
#include <iostream>

namespace nla {

void test_nla_intervals_basic() {
    std::cout << "test_nla_intervals_basic\n";
    
    lp::lar_solver s;
    reslimit rl;
    params_ref p;
    
    // Create variables with known intervals
    lpvar x = s.add_var(0, true);
    lpvar y = s.add_var(1, true);
    lpvar xy = s.add_var(2, true);
    
    solver nla_solver(s, p, rl);
    
    // Create monomial xy = x * y
    vector<lpvar> vars;
    vars.push_back(x);
    vars.push_back(y);
    nla_solver.add_monic(xy, vars.size(), vars.begin());
    
    // Set bounds: x in [1, 3], y in [2, 4]
    s.add_var_bound(x, lp::lconstraint_kind::GE, rational(1));
    s.add_var_bound(x, lp::lconstraint_kind::LE, rational(3));
    s.add_var_bound(y, lp::lconstraint_kind::GE, rational(2));
    s.add_var_bound(y, lp::lconstraint_kind::LE, rational(4));
    
    // xy should be in [2, 12]
    s.set_column_value_test(x, lp::impq(rational(2)));
    s.set_column_value_test(y, lp::impq(rational(3)));
    s.set_column_value_test(xy, lp::impq(rational(15))); // Outside valid range
    
    lbool result = nla_solver.get_core().test_check();
    VERIFY(result == l_false);
}

void test_nla_intervals_negative() {
    std::cout << "test_nla_intervals_negative\n";
    
    lp::lar_solver s;
    reslimit rl;
    params_ref p;
    
    lpvar x = s.add_var(0, true);
    lpvar y = s.add_var(1, true);
    lpvar xy = s.add_var(2, true);
    
    solver nla_solver(s, p, rl);
    
    vector<lpvar> vars;
    vars.push_back(x);
    vars.push_back(y);
    nla_solver.add_monic(xy, vars.size(), vars.begin());
    
    // Test with negative intervals: x in [-2, -1], y in [3, 5]
    s.add_var_bound(x, lp::lconstraint_kind::GE, rational(-2));
    s.add_var_bound(x, lp::lconstraint_kind::LE, rational(-1));
    s.add_var_bound(y, lp::lconstraint_kind::GE, rational(3));
    s.add_var_bound(y, lp::lconstraint_kind::LE, rational(5));
    
    // xy should be in [-10, -3]
    s.set_column_value_test(x, lp::impq(rational(-2)));
    s.set_column_value_test(y, lp::impq(rational(4)));
    s.set_column_value_test(xy, lp::impq(rational(-6))); // Valid value
    
    lbool result = nla_solver.get_core().test_check();
    VERIFY(result == l_true);
    
    // Now test invalid value
    s.set_column_value_test(xy, lp::impq(rational(1))); // Positive, should be negative
    result = nla_solver.get_core().test_check();
    VERIFY(result == l_false);
}

void test_nla_intervals_zero_crossing() {
    std::cout << "test_nla_intervals_zero_crossing\n";
    
    lp::lar_solver s;
    reslimit rl;
    params_ref p;
    
    lpvar x = s.add_var(0, true);
    lpvar y = s.add_var(1, true);
    lpvar xy = s.add_var(2, true);
    
    solver nla_solver(s, p, rl);
    
    vector<lpvar> vars;
    vars.push_back(x);
    vars.push_back(y);
    nla_solver.add_monic(xy, vars.size(), vars.begin());
    
    // Test intervals that cross zero: x in [-1, 2], y in [-3, 1]
    s.add_var_bound(x, lp::lconstraint_kind::GE, rational(-1));
    s.add_var_bound(x, lp::lconstraint_kind::LE, rational(2));
    s.add_var_bound(y, lp::lconstraint_kind::GE, rational(-3));
    s.add_var_bound(y, lp::lconstraint_kind::LE, rational(1));
    
    // xy should be in [-6, 3] (minimum at x=2, y=-3; maximum at x=2, y=1)
    s.set_column_value_test(x, lp::impq(rational(1)));
    s.set_column_value_test(y, lp::impq(rational(-2)));
    s.set_column_value_test(xy, lp::impq(rational(-2))); // Valid
    
    lbool result = nla_solver.get_core().test_check();
    VERIFY(result == l_true);
}

void test_nla_intervals_power() {
    std::cout << "test_nla_intervals_power\n";
    
    lp::lar_solver s;
    reslimit rl;
    params_ref p;
    
    lpvar x = s.add_var(0, true);
    lpvar x_squared = s.add_var(1, true);
    
    solver nla_solver(s, p, rl);
    
    // Create x^2 = x * x
    vector<lpvar> vars;
    vars.push_back(x);
    vars.push_back(x);
    nla_solver.add_monic(x_squared, vars.size(), vars.begin());
    
    // x in [-2, 3], so x^2 should be in [0, 9]
    s.add_var_bound(x, lp::lconstraint_kind::GE, rational(-2));
    s.add_var_bound(x, lp::lconstraint_kind::LE, rational(3));
    
    s.set_column_value_test(x, lp::impq(rational(-1)));
    s.set_column_value_test(x_squared, lp::impq(rational(1))); // Correct
    
    lbool result = nla_solver.get_core().test_check();
    VERIFY(result == l_true);
    
    // Test invalid value
    s.set_column_value_test(x_squared, lp::impq(rational(10))); // Too large
    result = nla_solver.get_core().test_check();
    VERIFY(result == l_false);
}

void test_nla_intervals_mixed_signs() {
    std::cout << "test_nla_intervals_mixed_signs\n";
    
    lp::lar_solver s;
    reslimit rl;
    params_ref p;
    
    lpvar x = s.add_var(0, true);
    lpvar y = s.add_var(1, true);
    lpvar z = s.add_var(2, true);
    lpvar xyz = s.add_var(3, true);
    
    solver nla_solver(s, p, rl);
    
    // Create xyz = x * y * z
    vector<lpvar> vars;
    vars.push_back(x);
    vars.push_back(y);
    vars.push_back(z);
    nla_solver.add_monic(xyz, vars.size(), vars.begin());
    
    // Mixed sign intervals
    s.add_var_bound(x, lp::lconstraint_kind::GE, rational(-1));
    s.add_var_bound(x, lp::lconstraint_kind::LE, rational(1));
    s.add_var_bound(y, lp::lconstraint_kind::GE, rational(2));
    s.add_var_bound(y, lp::lconstraint_kind::LE, rational(3));
    s.add_var_bound(z, lp::lconstraint_kind::GE, rational(-2));
    s.add_var_bound(z, lp::lconstraint_kind::LE, rational(-1));
    
    // xyz should be in [-6, 2]
    s.set_column_value_test(x, lp::impq(rational(1)));
    s.set_column_value_test(y, lp::impq(rational(3)));
    s.set_column_value_test(z, lp::impq(rational(-2)));
    s.set_column_value_test(xyz, lp::impq(rational(-6))); // Valid minimum
    
    lbool result = nla_solver.get_core().test_check();
    VERIFY(result == l_true);
}

void test_nla_intervals_fractional() {
    std::cout << "test_nla_intervals_fractional\n";
    
    lp::lar_solver s;
    reslimit rl;
    params_ref p;
    
    lpvar x = s.add_var(0, true);
    lpvar y = s.add_var(1, true);
    lpvar xy = s.add_var(2, true);
    
    solver nla_solver(s, p, rl);
    
    vector<lpvar> vars;
    vars.push_back(x);
    vars.push_back(y);
    nla_solver.add_monic(xy, vars.size(), vars.begin());
    
    // Test with fractional bounds
    s.add_var_bound(x, lp::lconstraint_kind::GE, rational(1, 2)); // 0.5
    s.add_var_bound(x, lp::lconstraint_kind::LE, rational(3, 2)); // 1.5
    s.add_var_bound(y, lp::lconstraint_kind::GE, rational(2, 3)); // ~0.67
    s.add_var_bound(y, lp::lconstraint_kind::LE, rational(4, 3)); // ~1.33
    
    s.set_column_value_test(x, lp::impq(rational(1)));
    s.set_column_value_test(y, lp::impq(rational(1)));
    s.set_column_value_test(xy, lp::impq(rational(1))); // Valid
    
    lbool result = nla_solver.get_core().test_check();
    VERIFY(result == l_true);
}

void test_nla_intervals() {
    test_nla_intervals_basic();
    test_nla_intervals_negative();
    test_nla_intervals_zero_crossing();
    test_nla_intervals_power();
    test_nla_intervals_mixed_signs();
    test_nla_intervals_fractional();
}

} // namespace nla

void tst_nla_intervals() {
    nla::test_nla_intervals();
}