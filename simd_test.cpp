/*
 * Simple SIMD optimization test for bitwise operations
 * Tests the performance of SIMD vs scalar bitwise operations
 */

#include <iostream>
#include <chrono>
#include <vector>
#include <random>
#include <iomanip>
#include <cstring>

#ifdef __SSE2__
#include <emmintrin.h>
#endif

// Simple test for SIMD bitwise operations on raw arrays
class SimdBitwiseTest {
private:
    static constexpr size_t ARRAY_SIZE = 1024; // 32-bit words
    static constexpr size_t NUM_ITERATIONS = 100000;

    std::vector<unsigned> array1;
    std::vector<unsigned> array2;
    std::vector<unsigned> result;

public:
    SimdBitwiseTest() {
        std::mt19937 rng(42); // Fixed seed for reproducible results

        array1.resize(ARRAY_SIZE);
        array2.resize(ARRAY_SIZE);
        result.resize(ARRAY_SIZE);

        // Fill with random data
        for (size_t i = 0; i < ARRAY_SIZE; ++i) {
            array1[i] = rng();
            array2[i] = rng();
        }
    }

    double benchmark_scalar_or() {
        auto start = std::chrono::high_resolution_clock::now();

        for (size_t iter = 0; iter < NUM_ITERATIONS; ++iter) {
            for (size_t i = 0; i < ARRAY_SIZE; ++i) {
                result[i] = array1[i] | array2[i];
            }
        }

        auto end = std::chrono::high_resolution_clock::now();
        return std::chrono::duration<double, std::milli>(end - start).count();
    }

#ifdef __SSE2__
    double benchmark_simd_or() {
        auto start = std::chrono::high_resolution_clock::now();

        const size_t simd_size = ARRAY_SIZE / 4;
        const __m128i* a_simd = reinterpret_cast<const __m128i*>(array1.data());
        const __m128i* b_simd = reinterpret_cast<const __m128i*>(array2.data());
        __m128i* result_simd = reinterpret_cast<__m128i*>(result.data());

        for (size_t iter = 0; iter < NUM_ITERATIONS; ++iter) {
            for (size_t i = 0; i < simd_size; ++i) {
                __m128i a = _mm_load_si128(&a_simd[i]);
                __m128i b = _mm_load_si128(&b_simd[i]);
                _mm_store_si128(&result_simd[i], _mm_or_si128(a, b));
            }
        }

        auto end = std::chrono::high_resolution_clock::now();
        return std::chrono::duration<double, std::milli>(end - start).count();
    }

    double benchmark_simd_and() {
        auto start = std::chrono::high_resolution_clock::now();

        const size_t simd_size = ARRAY_SIZE / 4;
        const __m128i* a_simd = reinterpret_cast<const __m128i*>(array1.data());
        const __m128i* b_simd = reinterpret_cast<const __m128i*>(array2.data());
        __m128i* result_simd = reinterpret_cast<__m128i*>(result.data());

        for (size_t iter = 0; iter < NUM_ITERATIONS; ++iter) {
            for (size_t i = 0; i < simd_size; ++i) {
                __m128i a = _mm_load_si128(&a_simd[i]);
                __m128i b = _mm_load_si128(&b_simd[i]);
                _mm_store_si128(&result_simd[i], _mm_and_si128(a, b));
            }
        }

        auto end = std::chrono::high_resolution_clock::now();
        return std::chrono::duration<double, std::milli>(end - start).count();
    }
#endif

    double benchmark_scalar_and() {
        auto start = std::chrono::high_resolution_clock::now();

        for (size_t iter = 0; iter < NUM_ITERATIONS; ++iter) {
            for (size_t i = 0; i < ARRAY_SIZE; ++i) {
                result[i] = array1[i] & array2[i];
            }
        }

        auto end = std::chrono::high_resolution_clock::now();
        return std::chrono::duration<double, std::milli>(end - start).count();
    }

    void run_benchmark() {
        std::cout << "=== SIMD Bitwise Operations Benchmark ===" << std::endl;
        std::cout << "Array size: " << ARRAY_SIZE << " words (" << (ARRAY_SIZE * 4) << " bytes)" << std::endl;
        std::cout << "Iterations: " << NUM_ITERATIONS << std::endl;

#ifdef __SSE2__
        std::cout << "SSE2 support: ENABLED" << std::endl;
#else
        std::cout << "SSE2 support: DISABLED" << std::endl;
#endif
        std::cout << std::endl;

        std::cout << std::fixed << std::setprecision(2);

        double scalar_or_time = benchmark_scalar_or();
        std::cout << "Scalar OR:  " << scalar_or_time << " ms" << std::endl;

#ifdef __SSE2__
        double simd_or_time = benchmark_simd_or();
        std::cout << "SIMD OR:    " << simd_or_time << " ms";
        if (simd_or_time > 0) {
            double or_speedup = scalar_or_time / simd_or_time;
            std::cout << " (speedup: " << or_speedup << "x)";
        }
        std::cout << std::endl;
#endif

        double scalar_and_time = benchmark_scalar_and();
        std::cout << "Scalar AND: " << scalar_and_time << " ms" << std::endl;

#ifdef __SSE2__
        double simd_and_time = benchmark_simd_and();
        std::cout << "SIMD AND:   " << simd_and_time << " ms";
        if (simd_and_time > 0) {
            double and_speedup = scalar_and_time / simd_and_time;
            std::cout << " (speedup: " << and_speedup << "x)";
        }
        std::cout << std::endl;
#endif

        std::cout << std::endl;
        std::cout << "Verification: ";
        // Quick verification that results are the same
        bool correct = true;
        std::vector<unsigned> scalar_result(ARRAY_SIZE);
        for (size_t i = 0; i < ARRAY_SIZE; ++i) {
            scalar_result[i] = array1[i] & array2[i];
        }

#ifdef __SSE2__
        // Run one SIMD AND operation for verification
        const size_t simd_size = ARRAY_SIZE / 4;
        const __m128i* a_simd = reinterpret_cast<const __m128i*>(array1.data());
        const __m128i* b_simd = reinterpret_cast<const __m128i*>(array2.data());
        __m128i* result_simd = reinterpret_cast<__m128i*>(result.data());

        for (size_t i = 0; i < simd_size; ++i) {
            __m128i a = _mm_load_si128(&a_simd[i]);
            __m128i b = _mm_load_si128(&b_simd[i]);
            _mm_store_si128(&result_simd[i], _mm_and_si128(a, b));
        }

        for (size_t i = 0; i < ARRAY_SIZE; ++i) {
            if (result[i] != scalar_result[i]) {
                correct = false;
                break;
            }
        }
#endif

        std::cout << (correct ? "PASSED" : "FAILED") << std::endl;
    }
};

int main() {
    try {
        SimdBitwiseTest test;
        test.run_benchmark();
        return 0;
    } catch (const std::exception& e) {
        std::cerr << "Error: " << e.what() << std::endl;
        return 1;
    }
}