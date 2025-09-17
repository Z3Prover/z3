#include <iostream>
#include <chrono>
#include <vector>
#include <string>
#include <random>
#include <cassert>
#include <iomanip>

// Include Z3's hash headers to test the actual implementation
#include "src/util/hash.h"

// Test with both enabled and disabled xxHash to measure improvement
unsigned string_hash_original_reference(const char * str, unsigned length, unsigned init_value);

// Performance test that measures Z3's actual hash function performance
class Z3HashPerformanceTest {
private:
    std::vector<std::string> test_data;
    std::mt19937 rng;

public:
    Z3HashPerformanceTest() : rng(42) {} // Fixed seed for reproducibility

    void generate_z3_realistic_data() {
        test_data.clear();

        // Generate data that represents realistic Z3 usage patterns

        // 1. Variable names and identifiers (short strings)
        for (int i = 0; i < 20000; ++i) {
            std::string var = "var_" + std::to_string(i);
            test_data.push_back(var);
        }

        // 2. SMT-LIB expressions (medium strings)
        for (int i = 0; i < 5000; ++i) {
            std::string expr = "(assert (and (> x_" + std::to_string(i) + " 0) (< y_" + std::to_string(i) + " 10)))";
            test_data.push_back(expr);
        }

        // 3. Larger formula fragments
        for (int i = 0; i < 1000; ++i) {
            std::string formula = "(assert (or ";
            for (int j = 0; j < 10; ++j) {
                formula += "(= term_" + std::to_string(i * 10 + j) + " value_" + std::to_string(j) + ") ";
            }
            formula += "))";
            test_data.push_back(formula);
        }

        // 4. Hash table keys (various lengths)
        std::uniform_int_distribution<> len_dist(8, 64);
        std::uniform_int_distribution<> char_dist(97, 122); // lowercase letters

        for (int i = 0; i < 10000; ++i) {
            int len = len_dist(rng);
            std::string key;
            key.reserve(len);
            for (int j = 0; j < len; ++j) {
                key.push_back(static_cast<char>(char_dist(rng)));
            }
            test_data.push_back(key);
        }

        std::cout << "Generated " << test_data.size() << " realistic Z3 hash test strings" << std::endl;
    }

    double benchmark_z3_hash_performance(int iterations = 50) {
        auto start = std::chrono::high_resolution_clock::now();

        volatile unsigned result = 0; // Prevent optimization
        for (int iter = 0; iter < iterations; ++iter) {
            for (const auto& str : test_data) {
                result += string_hash(str.c_str(), str.length(), 0);
            }
        }

        auto end = std::chrono::high_resolution_clock::now();
        auto duration = std::chrono::duration_cast<std::chrono::microseconds>(end - start);

        // Prevent dead code elimination
        if (result == 0xDEADBEEF) std::cout << "Impossible";

        return duration.count() / 1000.0; // Return milliseconds
    }

    void run_comprehensive_performance_test() {
        std::cout << "=== Z3 Hash Function Performance Analysis ===" << std::endl;
        std::cout << "Testing with realistic Z3 workload patterns" << std::endl;

        generate_z3_realistic_data();

        std::cout << "\n--- Performance Measurement (50 iterations) ---" << std::endl;
        double z3_time = benchmark_z3_hash_performance(50);

        std::cout << std::fixed << std::setprecision(3);
        std::cout << "Z3 Hash Function: " << z3_time << " ms" << std::endl;

        // Calculate throughput metrics
        size_t total_chars = 0;
        for (const auto& str : test_data) {
            total_chars += str.length();
        }

        double chars_per_ms = (total_chars * 50) / z3_time;
        double mb_per_sec = (chars_per_ms * 1000) / (1024 * 1024);

        std::cout << "Total characters processed: " << total_chars * 50 << std::endl;
        std::cout << "Throughput: " << chars_per_ms << " chars/ms" << std::endl;
        std::cout << "Throughput: " << mb_per_sec << " MB/sec" << std::endl;

        // Hash quality verification (basic collision test)
        std::cout << "\n--- Hash Quality Verification ---" << std::endl;
        verify_hash_quality();
    }

    void verify_hash_quality() {
        std::unordered_map<unsigned, int> hash_counts;
        int collisions = 0;

        for (const auto& str : test_data) {
            unsigned hash_val = string_hash(str.c_str(), str.length(), 0);
            hash_counts[hash_val]++;
            if (hash_counts[hash_val] == 2) {
                collisions++;
            }
        }

        double collision_rate = (100.0 * collisions) / test_data.size();
        std::cout << "Total strings: " << test_data.size() << std::endl;
        std::cout << "Unique hashes: " << hash_counts.size() << std::endl;
        std::cout << "Collisions: " << collisions << " (" << collision_rate << "%)" << std::endl;

        if (collision_rate < 5.0) {
            std::cout << "✓ Hash quality: Good (< 5% collision rate)" << std::endl;
        } else {
            std::cout << "⚠ Hash quality: Needs attention (>= 5% collision rate)" << std::endl;
        }
    }
};

// Build configuration info
void print_build_info() {
    std::cout << "=== Z3 Hash Function Build Configuration ===" << std::endl;

#ifdef Z3_USE_XXHASH
    #if Z3_USE_XXHASH
        std::cout << "xxHash optimization: ENABLED" << std::endl;
    #else
        std::cout << "xxHash optimization: DISABLED" << std::endl;
    #endif
#else
    std::cout << "xxHash optimization: NOT DEFINED (using default)" << std::endl;
#endif

    std::cout << "Compiler optimizations: " <<
#ifdef NDEBUG
        "ENABLED (-DNDEBUG)"
#else
        "DISABLED"
#endif
        << std::endl;
}

int main() {
    print_build_info();

    Z3HashPerformanceTest test;
    test.run_comprehensive_performance_test();

    return 0;
}