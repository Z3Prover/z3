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

static void test_bounded_roots() {
    for (unsigned p : {2u, 3u}) {
        for (unsigned mode = 0; mode < (p == 2 ? 3u : 2u); ++mode) {
            for (unsigned size = 0; size < 5; ++size) {
                lp::lar_solver s;
                reslimit rl;
                params_ref params;
                auto x = s.add_var(0, false);
                auto product = s.add_var(1, false);
                nla::core nonlinear(s, params, rl);
                nla::monomial_bounds bounds(&nonlinear);
                vector<lpvar> factors;
                for (unsigned i = 0; i < p; ++i)
                    factors.push_back(x);
                nonlinear.add_monic(product, p, factors.begin());

                rational root = size == 0 || size == 4 ? rational(2) : power(rational(2), size == 3 ? 255 / p : 130);
                if (size == 2 || size == 4)
                    root = rational(1) / root;
                if (p == 3 && mode == 0)
                    root = -root;
                rational value = power(root, p);
                auto bound = [&](lpvar v, lp::lconstraint_kind kind, rational const& q) {
                    s.activate(s.add_var_bound(v, kind, q));
                };
                bool product_lower = mode != 0;
                bound(product, product_lower ? lp::GE : lp::LE, value);
                if (p == 2 && mode == 1)
                    bound(x, lp::GE, rational(0));
                if (p == 2 && mode == 2)
                    bound(x, lp::LE, rational(0));
                s.find_feasible_solution();
                VERIFY(s.is_feasible());
                bounds.tighten_lp_bounds();

                bool expect_lower = p == 2 ? mode != 2 : mode == 1;
                bool expect_upper = p == 2 ? mode != 1 : mode == 0;
                if (size == 0 || size >= 3) {
                    if (expect_lower)
                        VERIFY(s.column_has_lower_bound(x) && s.get_lower_bound(x).x == (p == 2 && mode == 0 ? -root : root));
                    if (expect_upper)
                        VERIFY(s.column_has_upper_bound(x) && s.get_upper_bound(x).x == (p == 2 && mode == 2 ? -root : root));
                }
                else {
                    if (expect_lower)
                        VERIFY(!s.column_has_lower_bound(x) || s.get_lower_bound(x).x == rational(0));
                    if (expect_upper)
                        VERIFY(!s.column_has_upper_bound(x) || s.get_upper_bound(x).x == rational(0));
                }
            }
        }
    }

    for (unsigned p : {1u, 257u}) {
        lp::lar_solver s;
        reslimit rl;
        params_ref params;
        auto x = s.add_var(0, false);
        auto product = s.add_var(1, false);
        nla::core nonlinear(s, params, rl);
        nla::monomial_bounds bounds(&nonlinear);
        vector<lpvar> factors;
        for (unsigned i = 0; i < p; ++i)
            factors.push_back(x);
        if (p == 1) {
            auto y = s.add_var(2, false);
            factors.push_back(y);
            s.activate(s.add_var_bound(y, lp::GE, rational(1)));
            s.activate(s.add_var_bound(y, lp::LE, rational(1)));
        }
        nonlinear.add_monic(product, factors.size(), factors.begin());
        rational value = p == 1 ? power(rational(2), 300) : rational(1);
        s.activate(s.add_var_bound(product, lp::LE, value));
        s.find_feasible_solution();
        VERIFY(s.is_feasible());
        bounds.tighten_lp_bounds();
        if (p == 1) {
            VERIFY(s.column_has_upper_bound(x) && s.get_upper_bound(x).x == value);
        }
        else {
            VERIFY(!s.column_has_upper_bound(x));
        }
    }

    for (bool lower : {false, true}) {
        lp::lar_solver s;
        reslimit rl;
        params_ref params;
        auto x = s.add_var(0, false);
        auto product = s.add_var(1, false);
        nla::core nonlinear(s, params, rl);
        nla::monomial_bounds bounds(&nonlinear);
        lpvar factors[] = {x, x};
        nonlinear.add_monic(product, 2, factors);
        rational large = power(rational(2), 256);
        s.activate(s.add_var_bound(x, lower ? lp::GE : lp::LE, lower ? large : -large));
        s.find_feasible_solution();
        VERIFY(s.is_feasible());
        bounds.tighten_lp_bounds();
        VERIFY(!s.column_has_lower_bound(product));
    }
}

void test_monomial_bounds() {
    test_monomial_bounds_basic();
    test_monomial_bounds_propagation();
    test_monomial_bounds_intervals();
    test_monomial_bounds_power();
    test_monomial_bounds_linear_case();
    test_bounded_roots();
}

} // namespace nla

void tst_monomial_bounds() {
    nla::test_monomial_bounds();
}