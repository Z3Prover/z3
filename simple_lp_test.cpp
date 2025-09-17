#include <iostream>
#include <vector>
#include <chrono>
#include <random>
#include <cassert>

using namespace std;
using namespace std::chrono;

// Simplified test types
typedef double test_float;
typedef vector<test_float> test_vector;

// Original dot product implementation (for comparison)
test_float dot_product_original(const test_vector &a, const test_vector &b) {
    assert(a.size() == b.size());
    test_float r = 0.0;
    for (unsigned i = 0; i < a.size(); i++) {
        r += a[i] * b[i];
    }
    return r;
}

// Optimized dot product implementation
test_float dot_product_optimized(const test_vector &a, const test_vector &b) {
    assert(a.size() == b.size());
    test_float r = 0.0;
    const unsigned size = a.size();

    // Cache prefetch for large vectors
    if (size > 64) {
#ifdef __GNUC__
        __builtin_prefetch(&a[0], 0, 3);
        __builtin_prefetch(&b[0], 0, 3);
        if (size > 128) {
            __builtin_prefetch(&a[64], 0, 3);
            __builtin_prefetch(&b[64], 0, 3);
        }
#endif
    }

    // 4-way loop unrolling for better CPU throughput
    unsigned i = 0;
    const unsigned unroll_end = size & ~3u; // Round down to multiple of 4

    for (; i < unroll_end; i += 4) {
        r += a[i] * b[i] +
             a[i+1] * b[i+1] +
             a[i+2] * b[i+2] +
             a[i+3] * b[i+3];
    }

    // Handle remaining elements
    for (; i < size; i++) {
        r += a[i] * b[i];
    }

    return r;
}

// Original matrix update simulation
void matrix_update_original(test_vector &x_values, const test_vector &column_coeffs,
                          const vector<unsigned> &basis, const vector<unsigned> &column_vars,
                          test_float delta, unsigned leaving) {
    for (unsigned k = 0; k < column_vars.size(); k++) {
        const unsigned basis_var = basis[column_vars[k]];
        if (leaving != basis_var) {
            x_values[basis_var] += -delta * column_coeffs[k];
        }
    }
}

// Optimized matrix update simulation
void matrix_update_optimized(test_vector &x_values, const test_vector &column_coeffs,
                           const vector<unsigned> &basis, const vector<unsigned> &column_vars,
                           test_float delta, unsigned leaving) {
    const unsigned col_size = column_vars.size();

    // Cache prefetch for large columns
    if (col_size > 16) {
#ifdef __GNUC__
        __builtin_prefetch(&column_vars[0], 0, 3);
        __builtin_prefetch(&column_coeffs[0], 0, 3);
#endif
    }

    // Precompute -delta to avoid repeated negation
    const test_float neg_delta = -delta;

    // Optimized loop with better branch prediction
    for (unsigned k = 0; k < col_size; k++) {
        const unsigned basis_var = basis[column_vars[k]];
        if (leaving != basis_var) {
            x_values[basis_var] += neg_delta * column_coeffs[k];
        }
    }
}

void benchmark_dot_product() {
    const unsigned TEST_SIZE = 10000;
    const unsigned ITERATIONS = 1000;

    test_vector a(TEST_SIZE);
    test_vector b(TEST_SIZE);

    // Initialize with random values
    random_device rd;
    mt19937 gen(42); // Fixed seed for reproducible results
    uniform_real_distribution<test_float> dis(0.1, 100.0);

    for (unsigned i = 0; i < TEST_SIZE; i++) {
        a[i] = dis(gen);
        b[i] = dis(gen);
    }

    cout << "Benchmarking dot_product:" << endl;
    cout << "Vector size: " << TEST_SIZE << " elements, Iterations: " << ITERATIONS << endl;

    // Benchmark original
    auto start = high_resolution_clock::now();
    test_float result1 = 0;
    for (unsigned iter = 0; iter < ITERATIONS; iter++) {
        result1 = dot_product_original(a, b);
    }
    auto end = high_resolution_clock::now();
    auto duration1 = duration_cast<microseconds>(end - start);

    // Benchmark optimized
    start = high_resolution_clock::now();
    test_float result2 = 0;
    for (unsigned iter = 0; iter < ITERATIONS; iter++) {
        result2 = dot_product_optimized(a, b);
    }
    end = high_resolution_clock::now();
    auto duration2 = duration_cast<microseconds>(end - start);

    cout << "Original: " << duration1.count() << " μs, Result: " << result1 << endl;
    cout << "Optimized: " << duration2.count() << " μs, Result: " << result2 << endl;

    if (duration1.count() > 0) {
        double speedup = (double)duration1.count() / duration2.count();
        cout << "Speedup: " << speedup << "x" << endl;
    }
}

void benchmark_matrix_update() {
    const unsigned COLUMN_SIZE = 1000;
    const unsigned ITERATIONS = 5000;

    // Setup test data
    vector<unsigned> column_vars(COLUMN_SIZE);
    test_vector column_coeffs(COLUMN_SIZE);
    vector<unsigned> basis(COLUMN_SIZE);
    test_vector x_values1(COLUMN_SIZE);
    test_vector x_values2(COLUMN_SIZE);

    // Initialize test data
    random_device rd;
    mt19937 gen(42); // Fixed seed for reproducible results
    uniform_int_distribution<unsigned> var_dis(0, COLUMN_SIZE-1);
    uniform_real_distribution<test_float> coeff_dis(0.1, 5.0);

    for (unsigned i = 0; i < COLUMN_SIZE; i++) {
        column_vars[i] = i;
        column_coeffs[i] = coeff_dis(gen);
        basis[i] = var_dis(gen);
        x_values1[i] = x_values2[i] = coeff_dis(gen);
    }

    const test_float delta = 1.5;
    const unsigned leaving = COLUMN_SIZE / 2;

    cout << "\nBenchmarking matrix_update:" << endl;
    cout << "Column size: " << COLUMN_SIZE << " elements, Iterations: " << ITERATIONS << endl;

    // Benchmark original
    auto start = high_resolution_clock::now();
    for (unsigned iter = 0; iter < ITERATIONS; iter++) {
        matrix_update_original(x_values1, column_coeffs, basis, column_vars, delta, leaving);
    }
    auto end = high_resolution_clock::now();
    auto duration1 = duration_cast<microseconds>(end - start);

    // Benchmark optimized
    start = high_resolution_clock::now();
    for (unsigned iter = 0; iter < ITERATIONS; iter++) {
        matrix_update_optimized(x_values2, column_coeffs, basis, column_vars, delta, leaving);
    }
    end = high_resolution_clock::now();
    auto duration2 = duration_cast<microseconds>(end - start);

    cout << "Original: " << duration1.count() << " μs" << endl;
    cout << "Optimized: " << duration2.count() << " μs" << endl;

    if (duration1.count() > 0) {
        double speedup = (double)duration1.count() / duration2.count();
        cout << "Speedup: " << speedup << "x" << endl;
    }

    // Verify correctness
    test_float sum1 = 0, sum2 = 0;
    for (unsigned i = 0; i < COLUMN_SIZE; i++) {
        sum1 += x_values1[i];
        sum2 += x_values2[i];
    }
    cout << "Result verification: " << (abs(sum1 - sum2) < 1e-6 ? "PASS" : "FAIL") << endl;
}

int main() {
    cout << "=== Z3 Simplex Theory Solver Optimization Benchmark ===" << endl;
    cout << "Round 2: Linear Arithmetic Performance Improvements" << endl << endl;

    benchmark_dot_product();
    benchmark_matrix_update();

    cout << "\n=== Optimization Summary ===" << endl;
    cout << "- 4-way loop unrolling for dot product operations" << endl;
    cout << "- Cache prefetch hints for large vector/matrix operations" << endl;
    cout << "- Branch optimization and constant hoisting" << endl;

    return 0;
}