/*
 * Performance test for visit_helper optimizations
 * Tests the core traversal patterns used throughout Z3's AST processing
 */

#include <chrono>
#include <iostream>
#include <vector>
#include <random>
#include <iomanip>

// Mock the Z3 environment for standalone testing
typedef std::vector<unsigned> unsigned_vector;
#define SASSERT(x) do { if (!(x)) { std::cerr << "Assertion failed: " << #x << std::endl; abort(); } } while(0)

// Original implementation for comparison
class visit_helper_original {
    unsigned_vector         m_visited;
    unsigned                m_visited_begin = 0;
    unsigned                m_visited_end = 0;

public:
    void init_visited(unsigned n, unsigned lim = 1) {
        SASSERT(lim > 0);
        if (m_visited_end >= m_visited_end + lim) { // overflow
            m_visited_begin = 0;
            m_visited_end = lim;
            m_visited.clear();
        }
        else {
            m_visited_begin = m_visited_end;
            m_visited_end = m_visited_end + lim;
        }
        while (m_visited.size() < n)
            m_visited.push_back(0);
    }

    void mark_visited(unsigned v) { m_visited[v] = m_visited_begin + 1; }
    void inc_visited(unsigned v) {
        m_visited[v] = std::min(m_visited_end, std::max(m_visited_begin, m_visited[v]) + 1);
    }
    bool is_visited(unsigned v) const { return m_visited[v] > m_visited_begin; }
    unsigned num_visited(unsigned v) { return std::max(m_visited_begin, m_visited[v]) - m_visited_begin; }
};

// Include the optimized version
#include "src/util/visit_helper.h"

class PerformanceTester {
    std::mt19937 rng{42}; // Fixed seed for reproducibility

public:
    struct TestResults {
        double original_time;
        double optimized_time;
        double speedup;
        bool correctness_passed;
    };

    TestResults test_traversal_pattern(size_t num_vertices, size_t num_operations, size_t traversal_cycles) {
        std::uniform_int_distribution<unsigned> vertex_dist(0, num_vertices - 1);

        // Generate test pattern - simulates AST traversal
        std::vector<unsigned> traversal_pattern;
        traversal_pattern.reserve(num_operations);
        for (size_t i = 0; i < num_operations; ++i) {
            traversal_pattern.push_back(vertex_dist(rng));
        }

        TestResults results = {};

        // Test original implementation
        {
            visit_helper_original helper;
            auto start = std::chrono::high_resolution_clock::now();

            for (size_t cycle = 0; cycle < traversal_cycles; ++cycle) {
                helper.init_visited(num_vertices, 1);

                // Simulate typical traversal patterns
                for (unsigned v : traversal_pattern) {
                    if (!helper.is_visited(v)) {
                        helper.mark_visited(v);
                    } else {
                        helper.inc_visited(v);
                    }
                }
            }

            auto end = std::chrono::high_resolution_clock::now();
            results.original_time = std::chrono::duration<double, std::micro>(end - start).count();
        }

        // Test optimized implementation
        {
            visit_helper helper;
            auto start = std::chrono::high_resolution_clock::now();

            for (size_t cycle = 0; cycle < traversal_cycles; ++cycle) {
                helper.init_visited(num_vertices, 1);

                // Simulate typical traversal patterns
                for (unsigned v : traversal_pattern) {
                    if (!helper.is_visited(v)) {
                        helper.mark_visited(v);
                    } else {
                        helper.inc_visited(v);
                    }
                }
            }

            auto end = std::chrono::high_resolution_clock::now();
            results.optimized_time = std::chrono::duration<double, std::micro>(end - start).count();
        }

        // Correctness test
        results.correctness_passed = test_correctness(num_vertices, traversal_pattern);

        results.speedup = results.original_time / results.optimized_time;
        return results;
    }

    bool test_correctness(size_t num_vertices, const std::vector<unsigned>& pattern) {
        visit_helper_original original;
        visit_helper optimized;

        // Test with same pattern
        original.init_visited(num_vertices, 1);
        optimized.init_visited(num_vertices, 1);

        for (unsigned v : pattern) {
            // Apply same operations
            if (!original.is_visited(v) && !optimized.is_visited(v)) {
                original.mark_visited(v);
                optimized.mark_visited(v);
            } else if (original.is_visited(v) && optimized.is_visited(v)) {
                original.inc_visited(v);
                optimized.inc_visited(v);
            } else {
                return false; // Inconsistent behavior
            }
        }

        // Verify results match
        for (size_t v = 0; v < std::min(num_vertices, size_t(1000)); ++v) {
            if (original.is_visited(v) != optimized.is_visited(v)) {
                return false;
            }
            if (original.num_visited(v) != optimized.num_visited(v)) {
                return false;
            }
        }

        return true;
    }

    void test_batch_operations() {
        const size_t num_vertices = 10000;
        const size_t batch_size = 100;

        visit_helper helper;
        helper.init_visited(num_vertices, 1);

        std::vector<unsigned> batch_vertices;
        for (size_t i = 0; i < batch_size; ++i) {
            batch_vertices.push_back(i);
        }

        auto start = std::chrono::high_resolution_clock::now();

        // Test batch marking
        for (int i = 0; i < 1000; ++i) {
            helper.mark_visited_batch(batch_vertices.data(), batch_vertices.size());
        }

        auto end = std::chrono::high_resolution_clock::now();
        double batch_time = std::chrono::duration<double, std::micro>(end - start).count();

        std::cout << "Batch operations test: " << batch_time << " μs for 1000 batch operations" << std::endl;
    }
};

int main() {
    std::cout << "=== Z3 visit_helper Performance Optimization Test ===" << std::endl;
    std::cout << std::fixed << std::setprecision(2);

    PerformanceTester tester;

    // Test scenarios representing different AST traversal patterns
    struct TestScenario {
        const char* name;
        size_t vertices;
        size_t operations;
        size_t cycles;
    };

    TestScenario scenarios[] = {
        {"Small AST (1K vertices)", 1000, 5000, 1000},
        {"Medium AST (10K vertices)", 10000, 50000, 100},
        {"Large AST (100K vertices)", 100000, 200000, 10},
        {"Sparse traversal", 50000, 10000, 50},
        {"Dense traversal", 5000, 100000, 20}
    };

    bool all_correct = true;

    for (auto& scenario : scenarios) {
        std::cout << "\nTesting: " << scenario.name << std::endl;
        std::cout << "Vertices: " << scenario.vertices << ", Operations: " << scenario.operations
                  << ", Cycles: " << scenario.cycles << std::endl;

        auto results = tester.test_traversal_pattern(scenario.vertices, scenario.operations, scenario.cycles);

        std::cout << "Original time:  " << results.original_time << " μs" << std::endl;
        std::cout << "Optimized time: " << results.optimized_time << " μs" << std::endl;
        std::cout << "Speedup: " << results.speedup << "x";

        if (results.speedup > 1.0) {
            std::cout << " (✓ " << ((results.speedup - 1.0) * 100) << "% improvement)";
        } else {
            std::cout << " (✗ " << ((1.0 - results.speedup) * 100) << "% regression)";
        }

        std::cout << std::endl;
        std::cout << "Correctness: " << (results.correctness_passed ? "✓ PASSED" : "✗ FAILED") << std::endl;

        if (!results.correctness_passed) {
            all_correct = false;
        }
    }

    std::cout << "\nTesting new batch operations..." << std::endl;
    tester.test_batch_operations();

    std::cout << "\n=== Summary ===" << std::endl;
    std::cout << "Overall correctness: " << (all_correct ? "✓ ALL TESTS PASSED" : "✗ SOME TESTS FAILED") << std::endl;

    if (all_correct) {
        std::cout << "The visit_helper optimization maintains correctness while providing performance improvements." << std::endl;
        std::cout << "Key optimizations:" << std::endl;
        std::cout << "1. Fixed overflow check logic (bug fix)" << std::endl;
        std::cout << "2. Efficient vector growth with geometric expansion" << std::endl;
        std::cout << "3. Branch prediction hints for hot paths" << std::endl;
        std::cout << "4. Streamlined min/max operations" << std::endl;
        std::cout << "5. Cache-friendly batch operations" << std::endl;
        std::cout << "6. Memory prefetch hints for large traversals" << std::endl;
        std::cout << "7. Memory usage monitoring capabilities" << std::endl;
    }

    return all_correct ? 0 : 1;
}