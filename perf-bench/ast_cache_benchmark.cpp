#include <chrono>
#include <iostream>
#include <vector>
#include "ast/ast.h"

// Simple benchmark to test AST creation and hash lookup performance
class ast_cache_benchmark {
private:
    ast_manager m_manager;
    std::vector<expr*> m_exprs;

public:
    void setup(int num_expressions) {
        // Create a variety of expressions to test hash table performance
        sort* int_sort = m_manager.mk_int_sort();

        for (int i = 0; i < num_expressions; ++i) {
            // Create various expressions with different structures
            if (i % 3 == 0) {
                // Create constant expressions
                expr* val = m_manager.mk_numeral(i, int_sort);
                m_exprs.push_back(val);
            } else if (i % 3 == 1) {
                // Create variable expressions
                expr* var = m_manager.mk_var(i, int_sort);
                m_exprs.push_back(var);
            } else {
                // Create app expressions (most common and performance-critical)
                if (i > 0) {
                    expr* prev = m_exprs[i - 1];
                    expr* val = m_manager.mk_numeral(1, int_sort);
                    expr* add_expr = m_manager.mk_add(prev, val);
                    m_exprs.push_back(add_expr);
                } else {
                    expr* val = m_manager.mk_numeral(0, int_sort);
                    m_exprs.push_back(val);
                }
            }
        }
    }

    double benchmark_hash_lookups(int iterations) {
        auto start = std::chrono::high_resolution_clock::now();

        // Simulate heavy hash table usage - the primary bottleneck mentioned by maintainer
        unsigned total_hash = 0;
        for (int iter = 0; iter < iterations; ++iter) {
            for (expr* e : m_exprs) {
                // Hash computation and lookup simulation
                total_hash += e->hash();
                // Simulate additional cache-sensitive operations
                total_hash += e->get_kind();
                if (is_app(e)) {
                    app* a = to_app(e);
                    total_hash += a->get_decl()->hash();
                    total_hash += a->get_num_args();
                }
            }
        }

        auto end = std::chrono::high_resolution_clock::now();
        auto duration = std::chrono::duration_cast<std::chrono::microseconds>(end - start);

        // Prevent compiler optimization
        std::cout << "Hash sum (ignore): " << total_hash << std::endl;

        return duration.count() / 1000.0; // Convert to milliseconds
    }

    void cleanup() {
        // Clean up expressions
        for (expr* e : m_exprs) {
            m_manager.dec_ref(e);
        }
        m_exprs.clear();
    }
};

int main() {
    std::cout << "AST Cache Optimization Benchmark" << std::endl;
    std::cout << "=================================" << std::endl;

    ast_cache_benchmark bench;

    const int num_expressions = 10000;
    const int num_iterations = 100;

    std::cout << "Setting up " << num_expressions << " expressions..." << std::endl;
    bench.setup(num_expressions);

    std::cout << "Running hash lookup benchmark (" << num_iterations << " iterations)..." << std::endl;
    double time_ms = bench.benchmark_hash_lookups(num_iterations);

    std::cout << "Results:" << std::endl;
    std::cout << "  Total time: " << time_ms << " ms" << std::endl;
    std::cout << "  Time per expression: " << (time_ms / (num_expressions * num_iterations)) << " ms" << std::endl;
    std::cout << "  Operations per second: " << ((num_expressions * num_iterations * 1000.0) / time_ms) << std::endl;

    bench.cleanup();

    return 0;
}