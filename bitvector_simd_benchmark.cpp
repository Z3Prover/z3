/*
 * SIMD BitVector Performance Benchmark
 * Tests the performance improvements from SIMD-optimized bitwise operations
 */

#include <iostream>
#include <chrono>
#include <vector>
#include <random>
#include <iomanip>
#include "src/util/bit_vector.h"

class PerformanceBenchmark {
private:
    static constexpr size_t NUM_ITERATIONS = 10000;
    static constexpr size_t BIT_VECTOR_SIZE = 1024; // 32 words = good for SIMD

    std::vector<bit_vector> test_vectors;
    std::mt19937 rng;

public:
    PerformanceBenchmark() : rng(std::random_device{}()) {
        // Create test vectors with random data
        test_vectors.reserve(100);
        for (int i = 0; i < 100; ++i) {
            bit_vector bv(BIT_VECTOR_SIZE);

            // Fill with random bits
            for (size_t j = 0; j < BIT_VECTOR_SIZE; ++j) {
                bv.push_back(rng() % 2 == 0);
            }
            test_vectors.push_back(std::move(bv));
        }
    }

    double benchmark_or_operation() {
        auto start = std::chrono::high_resolution_clock::now();

        for (size_t iter = 0; iter < NUM_ITERATIONS; ++iter) {
            bit_vector result = test_vectors[0];
            for (size_t i = 1; i < test_vectors.size(); ++i) {
                result |= test_vectors[i];
            }

            // Prevent optimization
            volatile unsigned hash = result.get_hash();
            (void)hash;
        }

        auto end = std::chrono::high_resolution_clock::now();
        return std::chrono::duration<double, std::milli>(end - start).count();
    }

    double benchmark_and_operation() {
        auto start = std::chrono::high_resolution_clock::now();

        for (size_t iter = 0; iter < NUM_ITERATIONS; ++iter) {
            bit_vector result = test_vectors[0];
            for (size_t i = 1; i < test_vectors.size(); ++i) {
                result &= test_vectors[i];
            }

            // Prevent optimization
            volatile unsigned hash = result.get_hash();
            (void)hash;
        }

        auto end = std::chrono::high_resolution_clock::now();
        return std::chrono::duration<double, std::milli>(end - start).count();
    }

    double benchmark_equality_operation() {
        auto start = std::chrono::high_resolution_clock::now();

        size_t equal_count = 0;
        for (size_t iter = 0; iter < NUM_ITERATIONS; ++iter) {
            for (size_t i = 0; i < test_vectors.size(); ++i) {
                for (size_t j = i + 1; j < test_vectors.size(); ++j) {
                    if (test_vectors[i] == test_vectors[j]) {
                        equal_count++;
                    }
                }
            }
        }

        // Prevent optimization
        volatile size_t count = equal_count;
        (void)count;

        auto end = std::chrono::high_resolution_clock::now();
        return std::chrono::duration<double, std::milli>(end - start).count();
    }

    double benchmark_negation_operation() {
        auto start = std::chrono::high_resolution_clock::now();

        for (size_t iter = 0; iter < NUM_ITERATIONS; ++iter) {
            for (size_t i = 0; i < test_vectors.size(); ++i) {
                bit_vector copy = test_vectors[i];
                copy.neg();

                // Prevent optimization
                volatile unsigned hash = copy.get_hash();
                (void)hash;
            }
        }

        auto end = std::chrono::high_resolution_clock::now();
        return std::chrono::duration<double, std::milli>(end - start).count();
    }

    void print_system_info() {
        std::cout << "=== BitVector SIMD Optimization Benchmark ===" << std::endl;
        std::cout << "Test Configuration:" << std::endl;
        std::cout << "  - BitVector size: " << BIT_VECTOR_SIZE << " bits ("
                  << (BIT_VECTOR_SIZE/32) << " words)" << std::endl;
        std::cout << "  - Number of test vectors: " << test_vectors.size() << std::endl;
        std::cout << "  - Iterations per test: " << NUM_ITERATIONS << std::endl;

#ifdef __SSE2__
        std::cout << "  - SIMD optimization: ENABLED (SSE2)" << std::endl;
#else
        std::cout << "  - SIMD optimization: DISABLED (scalar only)" << std::endl;
#endif
        std::cout << std::endl;
    }

    void run_benchmark() {
        print_system_info();

        std::cout << "Running performance benchmarks..." << std::endl;
        std::cout << std::fixed << std::setprecision(2);

        double or_time = benchmark_or_operation();
        std::cout << "OR operation:       " << or_time << " ms" << std::endl;

        double and_time = benchmark_and_operation();
        std::cout << "AND operation:      " << and_time << " ms" << std::endl;

        double eq_time = benchmark_equality_operation();
        std::cout << "Equality operation: " << eq_time << " ms" << std::endl;

        double neg_time = benchmark_negation_operation();
        std::cout << "Negation operation: " << neg_time << " ms" << std::endl;

        double total_time = or_time + and_time + eq_time + neg_time;
        std::cout << std::endl;
        std::cout << "Total benchmark time: " << total_time << " ms" << std::endl;
    }
};

int main() {
    try {
        PerformanceBenchmark benchmark;
        benchmark.run_benchmark();
        return 0;
    } catch (const std::exception& e) {
        std::cerr << "Error: " << e.what() << std::endl;
        return 1;
    }
}