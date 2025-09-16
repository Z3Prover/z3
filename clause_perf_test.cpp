#include <iostream>
#include <chrono>
#include <random>
#include <vector>
#include "src/sat/sat_clause.h"
#include "src/sat/sat_types.h"

using namespace sat;

class clause_performance_test {
private:
    clause_allocator allocator;
    std::vector<clause*> test_clauses;
    std::vector<literal> test_literals;
    std::mt19937 rng;

    // Performance counters
    unsigned long contains_literal_calls = 0;
    unsigned long contains_var_calls = 0;
    unsigned long satisfied_calls = 0;

public:
    clause_performance_test() : rng(42) {
        // Generate test literals
        for (unsigned v = 0; v < 1000; v++) {
            test_literals.push_back(literal(v, false));
            test_literals.push_back(literal(v, true));
        }

        // Generate test clauses of various sizes
        create_test_clauses();
    }

    ~clause_performance_test() {
        for (clause* c : test_clauses) {
            allocator.del_clause(c);
        }
    }

    void create_test_clauses() {
        std::uniform_int_distribution<unsigned> size_dist(2, 20);
        std::uniform_int_distribution<unsigned> lit_dist(0, test_literals.size() - 1);

        // Create 10000 test clauses
        for (int i = 0; i < 10000; i++) {
            unsigned size = size_dist(rng);
            std::vector<literal> clause_lits;

            for (unsigned j = 0; j < size; j++) {
                clause_lits.push_back(test_literals[lit_dist(rng)]);
            }

            clause* c = allocator.mk_clause(size, clause_lits.data(), i % 2 == 0);
            test_clauses.push_back(c);
        }

        std::cout << "Created " << test_clauses.size() << " test clauses" << std::endl;

        // Check cache alignment effectiveness
        unsigned aligned_count = 0;
        for (clause* c : test_clauses) {
            if (c->is_cache_aligned()) aligned_count++;
        }
        std::cout << "Cache-aligned clauses: " << aligned_count << "/" << test_clauses.size()
                  << " (" << (100.0 * aligned_count / test_clauses.size()) << "%)" << std::endl;
    }

    void benchmark_contains_literal() {
        std::uniform_int_distribution<unsigned> clause_dist(0, test_clauses.size() - 1);
        std::uniform_int_distribution<unsigned> lit_dist(0, test_literals.size() - 1);

        const int iterations = 1000000;
        unsigned hits = 0;

        auto start = std::chrono::high_resolution_clock::now();

        for (int i = 0; i < iterations; i++) {
            clause* c = test_clauses[clause_dist(rng)];
            literal l = test_literals[lit_dist(rng)];
            if (c->contains(l)) hits++;
            contains_literal_calls++;
        }

        auto end = std::chrono::high_resolution_clock::now();
        auto duration = std::chrono::duration_cast<std::chrono::nanoseconds>(end - start);

        std::cout << "contains(literal) benchmark:" << std::endl;
        std::cout << "  Iterations: " << iterations << std::endl;
        std::cout << "  Hits: " << hits << " (" << (100.0 * hits / iterations) << "%)" << std::endl;
        std::cout << "  Total time: " << duration.count() / 1e6 << " ms" << std::endl;
        std::cout << "  Average time per call: " << (double)duration.count() / iterations << " ns" << std::endl;
    }

    void benchmark_contains_var() {
        std::uniform_int_distribution<unsigned> clause_dist(0, test_clauses.size() - 1);
        std::uniform_int_distribution<unsigned> var_dist(0, 999);

        const int iterations = 1000000;
        unsigned hits = 0;

        auto start = std::chrono::high_resolution_clock::now();

        for (int i = 0; i < iterations; i++) {
            clause* c = test_clauses[clause_dist(rng)];
            bool_var v = var_dist(rng);
            if (c->contains(v)) hits++;
            contains_var_calls++;
        }

        auto end = std::chrono::high_resolution_clock::now();
        auto duration = std::chrono::duration_cast<std::chrono::nanoseconds>(end - start);

        std::cout << "contains(bool_var) benchmark:" << std::endl;
        std::cout << "  Iterations: " << iterations << std::endl;
        std::cout << "  Hits: " << hits << " (" << (100.0 * hits / iterations) << "%)" << std::endl;
        std::cout << "  Total time: " << duration.count() / 1e6 << " ms" << std::endl;
        std::cout << "  Average time per call: " << (double)duration.count() / iterations << " ns" << std::endl;
    }

    void benchmark_satisfied_by() {
        // Create a simple model
        model m(1000);
        std::uniform_int_distribution<int> bool_dist(0, 2); // 0=false, 1=true, 2=undef

        for (unsigned v = 0; v < 1000; v++) {
            int val = bool_dist(rng);
            m[v] = (val == 0) ? l_false : (val == 1) ? l_true : l_undef;
        }

        std::uniform_int_distribution<unsigned> clause_dist(0, test_clauses.size() - 1);

        const int iterations = 500000;
        unsigned satisfied = 0;

        auto start = std::chrono::high_resolution_clock::now();

        for (int i = 0; i < iterations; i++) {
            clause* c = test_clauses[clause_dist(rng)];
            if (c->satisfied_by(m)) satisfied++;
            satisfied_calls++;
        }

        auto end = std::chrono::high_resolution_clock::now();
        auto duration = std::chrono::duration_cast<std::chrono::nanoseconds>(end - start);

        std::cout << "satisfied_by(model) benchmark:" << std::endl;
        std::cout << "  Iterations: " << iterations << std::endl;
        std::cout << "  Satisfied: " << satisfied << " (" << (100.0 * satisfied / iterations) << "%)" << std::endl;
        std::cout << "  Total time: " << duration.count() / 1e6 << " ms" << std::endl;
        std::cout << "  Average time per call: " << (double)duration.count() / iterations << " ns" << std::endl;
    }

    void run_all_benchmarks() {
        std::cout << "=== Z3 Clause Management Performance Test ===" << std::endl;
        std::cout << "Testing cache-friendly optimizations" << std::endl;
        std::cout << std::endl;

        benchmark_contains_literal();
        std::cout << std::endl;

        benchmark_contains_var();
        std::cout << std::endl;

        benchmark_satisfied_by();
        std::cout << std::endl;

        // Memory usage info
        std::cout << "Memory usage:" << std::endl;
        std::cout << "  Clause allocator size: " << allocator.get_allocation_size() << " bytes" << std::endl;
        std::cout << "  Average clause size: " << (double)allocator.get_allocation_size() / test_clauses.size() << " bytes" << std::endl;
    }
};

int main() {
    try {
        clause_performance_test test;
        test.run_all_benchmarks();
        return 0;
    } catch (const std::exception& e) {
        std::cerr << "Error: " << e.what() << std::endl;
        return 1;
    }
}