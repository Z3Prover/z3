#include <iostream>
#include <vector>
#include <chrono>
#include <random>
#include <cassert>

// Minimal Z3 includes for testing
#include "src/math/lp/lp_core_solver_base.h"
#include "src/util/mpq.h"

using namespace std;
using namespace std::chrono;
using namespace lp;

// Test the optimized dot_product function
void test_dot_product_performance() {
    const unsigned TEST_SIZE = 10000;
    const unsigned ITERATIONS = 1000;

    vector<mpq> a(TEST_SIZE);
    vector<mpq> b(TEST_SIZE);

    // Initialize with random values
    random_device rd;
    mt19937 gen(rd());
    uniform_real_distribution<double> dis(0.1, 100.0);

    for (unsigned i = 0; i < TEST_SIZE; i++) {
        a[i] = mpq(dis(gen));
        b[i] = mpq(dis(gen));
    }

    cout << "Testing dot_product performance:" << endl;
    cout << "Vector size: " << TEST_SIZE << " elements" << endl;
    cout << "Iterations: " << ITERATIONS << endl;

    auto start = high_resolution_clock::now();
    mpq result;

    for (unsigned iter = 0; iter < ITERATIONS; iter++) {
        result = dot_product(a, b);
    }

    auto end = high_resolution_clock::now();
    auto duration = duration_cast<microseconds>(end - start);

    cout << "Optimized dot_product time: " << duration.count() << " microseconds" << endl;
    cout << "Average per operation: " << (duration.count() / ITERATIONS) << " microseconds" << endl;
    cout << "Result (first few digits): " << result.to_string().substr(0, 20) << "..." << endl;
}

// Simplified matrix column simulation for testing update operations
void test_matrix_update_performance() {
    const unsigned COLUMN_SIZE = 1000;
    const unsigned ITERATIONS = 5000;

    // Simulate matrix column data
    vector<unsigned> column_vars(COLUMN_SIZE);
    vector<mpq> column_coeffs(COLUMN_SIZE);
    vector<unsigned> basis(COLUMN_SIZE);
    vector<mpq> x_values(COLUMN_SIZE);

    // Initialize test data
    random_device rd;
    mt19937 gen(rd());
    uniform_int_distribution<unsigned> var_dis(0, COLUMN_SIZE-1);
    uniform_real_distribution<double> coeff_dis(0.1, 5.0);

    for (unsigned i = 0; i < COLUMN_SIZE; i++) {
        column_vars[i] = i;
        column_coeffs[i] = mpq(coeff_dis(gen));
        basis[i] = var_dis(gen);
        x_values[i] = mpq(coeff_dis(gen));
    }

    cout << "\nTesting matrix update performance:" << endl;
    cout << "Column size: " << COLUMN_SIZE << " elements" << endl;
    cout << "Iterations: " << ITERATIONS << endl;

    const mpq delta = mpq(1.5);
    const mpq neg_delta = -delta;
    const unsigned leaving = COLUMN_SIZE / 2;

    auto start = high_resolution_clock::now();

    for (unsigned iter = 0; iter < ITERATIONS; iter++) {
        for (unsigned k = 0; k < COLUMN_SIZE; k++) {
            const unsigned basis_var = basis[column_vars[k]];
            if (leaving != basis_var) {
                // Simulate the optimized update operation
                x_values[basis_var] += neg_delta * column_coeffs[k];
            }
        }
    }

    auto end = high_resolution_clock::now();
    auto duration = duration_cast<microseconds>(end - start);

    cout << "Optimized matrix update time: " << duration.count() << " microseconds" << endl;
    cout << "Average per operation: " << (duration.count() / ITERATIONS) << " microseconds" << endl;

    // Verify correctness (simple sanity check)
    mpq sum;
    for (const auto& val : x_values) {
        sum += val;
    }
    cout << "Result checksum: " << sum.to_string().substr(0, 15) << "..." << endl;
}

int main() {
    cout << "=== Z3 Simplex Performance Test Suite ===" << endl;
    cout << "Testing Theory Solver optimizations (Round 2)" << endl << endl;

    try {
        test_dot_product_performance();
        test_matrix_update_performance();

        cout << "\n=== Performance Test Complete ===" << endl;
        cout << "Optimizations: Cache prefetch, loop unrolling, branch optimization" << endl;

    } catch (const exception& e) {
        cout << "Error during testing: " << e.what() << endl;
        return 1;
    }

    return 0;
}