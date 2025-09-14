/*++
Copyright (c) 2024 Microsoft Corporation

Module Name:

    monomial_bounds.cpp

Abstract:

    Tests for monomial bounds functionality in math/lp

Author:

    Test Coverage Improvement

Revision History:

--*/

#include "math/lp/monomial_bounds.h"
#include "math/lp/nla_core.h"
#include "math/lp/lar_solver.h"
#include "util/rational.h"
#include "util/rlimit.h"

namespace nla {

void test_monomial_bounds_basic() {
    std::cout << "test_monomial_bounds_basic\n";
    
    lp::lar_solver s;
    reslimit rl;
    params_ref p;
    
    // Create variables x, y, z and their product xyz
    lpvar x = s.add_var(0, true);
    lpvar y = s.add_var(1, true);  
    lpvar z = s.add_var(2, true);
    lpvar xyz = s.add_var(3, true);
    
    // Set up solver with monomial bounds
    nla::core nla_solver(s, p, rl);
    
    // Create monomial xyz = x * y * z
    vector<lpvar> vars;
    vars.push_back(x);
    vars.push_back(y);
    vars.push_back(z);
    nla_solver.add_monic(xyz, vars.size(), vars.begin());
    
    // Set values that are consistent with monomial constraint
    s.set_column_value_test(x, lp::impq(rational(2)));
    s.set_column_value_test(y, lp::impq(rational(3)));
    s.set_column_value_test(z, lp::impq(rational(4)));
    s.set_column_value_test(xyz, lp::impq(rational(24))); // 2*3*4 = 24
    
    // Test that this is consistent
    lbool result = nla_solver.test_check();
    VERIFY(result != l_false); // Should be satisfiable or unknown
}

void test_monomial_bounds_propagation() {
    std::cout << "test_monomial_bounds_propagation\n";
    
    lp::lar_solver s;
    reslimit rl;
    params_ref p;
    
    // Create variables for testing bound propagation
    lpvar x = s.add_var(0, true);
    lpvar y = s.add_var(1, true);
    lpvar xy = s.add_var(2, true);
    
    nla::core nla_solver(s, p, rl);
    
    // Create monomial xy = x * y
    vector<lpvar> vars;
    vars.push_back(x);
    vars.push_back(y);
    nla_solver.add_monic(xy, vars.size(), vars.begin());
    
    // Test case where one variable is zero - should produce xy = 0
    s.set_column_value_test(x, lp::impq(rational(0)));
    s.set_column_value_test(y, lp::impq(rational(5)));
    s.set_column_value_test(xy, lp::impq(rational(0))); // 0 * 5 = 0
    
    lbool result = nla_solver.test_check();
    VERIFY(result != l_false); // Should be consistent
}

void test_monomial_bounds_intervals() {
    std::cout << "test_monomial_bounds_intervals\n";
    
    lp::lar_solver s;
    reslimit rl;
    params_ref p;
    
    // Test interval-based monomial bounds
    lpvar a = s.add_var(0, true);
    lpvar b = s.add_var(1, true);
    lpvar ab = s.add_var(2, true);
    
    nla::core nla_solver(s, p, rl);
    
    vector<lpvar> vars;
    vars.push_back(a);
    vars.push_back(b);
    nla_solver.add_monic(ab, vars.size(), vars.begin());
    
    // Set up consistent bounds on variables
    s.set_column_value_test(a, lp::impq(rational(1), rational(2))); // 0.5
    s.set_column_value_test(b, lp::impq(rational(3), rational(2))); // 1.5
    s.set_column_value_test(ab, lp::impq(rational(3), rational(4))); // 0.5 * 1.5 = 0.75
    
    lbool result = nla_solver.test_check();
    VERIFY(result != l_false); // Should be consistent
}

void test_monomial_bounds_power() {
    std::cout << "test_monomial_bounds_power\n";
    
    lp::lar_solver s;
    reslimit rl;
    params_ref p;
    
    // Test power/repeated variable cases
    lpvar x = s.add_var(0, true);
    lpvar x_squared = s.add_var(1, true);
    
    nla::core nla_solver(s, p, rl);
    
    // Create x^2 = x * x
    vector<lpvar> vars;
    vars.push_back(x);
    vars.push_back(x);
    nla_solver.add_monic(x_squared, vars.size(), vars.begin());
    
    // Test with negative value
    s.set_column_value_test(x, lp::impq(rational(-3)));
    s.set_column_value_test(x_squared, lp::impq(rational(9))); // (-3)^2 = 9
    
    lbool result = nla_solver.test_check();
    VERIFY(result != l_false); // Should be consistent
}

void test_monomial_bounds_linear_case() {
    std::cout << "test_monomial_bounds_linear_case\n";
    
    lp::lar_solver s;
    reslimit rl;
    params_ref p;
    
    // Test linear monomial (degree 1)
    lpvar x = s.add_var(0, true);
    lpvar mx = s.add_var(1, true); // monomial of just x
    
    nla::core nla_solver(s, p, rl);
    
    vector<lpvar> vars;
    vars.push_back(x);
    nla_solver.add_monic(mx, vars.size(), vars.begin());
    
    s.set_column_value_test(x, lp::impq(rational(7)));
    s.set_column_value_test(mx, lp::impq(rational(7))); // mx = x = 7 (linear case)
    
    lbool result = nla_solver.test_check();
    VERIFY(result != l_false); // Should be consistent
}

void test_monomial_bounds() {
    test_monomial_bounds_basic();
    test_monomial_bounds_propagation();
    test_monomial_bounds_intervals();
    test_monomial_bounds_power();
    test_monomial_bounds_linear_case();
}

} // namespace nla

void tst_monomial_bounds() {
    nla::test_monomial_bounds();
}