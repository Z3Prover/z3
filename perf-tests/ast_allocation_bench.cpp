#include "ast/ast.h"
#include "util/timeit.h"
#include <iostream>
#include <vector>
#include <chrono>

/*
 * Micro-benchmark to measure AST allocation performance
 * This will help establish baseline performance before optimization
 */

static double get_time_seconds() {
    auto now = std::chrono::high_resolution_clock::now();
    auto duration = now.time_since_epoch();
    return std::chrono::duration_cast<std::chrono::microseconds>(duration).count() / 1000000.0;
}

void benchmark_app_allocation(ast_manager& m, unsigned num_iterations) {
    std::cout << "Benchmarking app allocation (" << num_iterations << " iterations)...\n";

    // Create some basic sorts for testing
    sort* bool_sort = m.mk_bool_sort();
    sort* int_sort = m.mk_int_sort();

    // Create some basic function declarations for different arities
    func_decl* unary_func = m.mk_func_decl(symbol("unary"), int_sort, bool_sort);
    func_decl* binary_func = m.mk_func_decl(symbol("binary"), int_sort, int_sort, bool_sort);
    func_decl* ternary_func = m.mk_func_decl(symbol("ternary"), int_sort, int_sort, int_sort, bool_sort);

    // Create some variables for testing
    std::vector<var*> vars;
    for (unsigned i = 0; i < 10; ++i) {
        vars.push_back(m.mk_var(i, int_sort));
    }

    double start_time = get_time_seconds();
    std::vector<app*> apps;
    apps.reserve(num_iterations * 3);

    // Benchmark allocation of apps with different arities
    for (unsigned i = 0; i < num_iterations; ++i) {
        // Unary apps (common case)
        apps.push_back(m.mk_app(unary_func, vars[i % vars.size()]));

        // Binary apps (very common case)
        apps.push_back(m.mk_app(binary_func, vars[i % vars.size()], vars[(i+1) % vars.size()]));

        // Ternary apps (less common but still frequent)
        apps.push_back(m.mk_app(ternary_func, vars[i % vars.size()], vars[(i+1) % vars.size()], vars[(i+2) % vars.size()]));
    }

    double end_time = get_time_seconds();
    double elapsed = end_time - start_time;

    std::cout << "Created " << apps.size() << " app nodes in " << elapsed << " seconds\n";
    std::cout << "Rate: " << (apps.size() / elapsed) << " allocations/sec\n";
    std::cout << "Average time per allocation: " << (elapsed * 1000000.0 / apps.size()) << " microseconds\n";

    // Report memory usage
    std::cout << "Total allocated size: " << m.get_allocation_size() << " bytes\n";
}

void benchmark_mixed_allocation(ast_manager& m, unsigned num_iterations) {
    std::cout << "\nBenchmarking mixed AST allocation (" << num_iterations << " iterations)...\n";

    sort* bool_sort = m.mk_bool_sort();
    sort* int_sort = m.mk_int_sort();

    double start_time = get_time_seconds();
    std::vector<ast*> nodes;
    nodes.reserve(num_iterations * 4);

    for (unsigned i = 0; i < num_iterations; ++i) {
        // Mix of common AST node types
        nodes.push_back(m.mk_var(i, int_sort));  // var allocation
        nodes.push_back(m.mk_const(symbol(std::to_string(i).c_str()), int_sort)); // simple app
        nodes.push_back(m.mk_eq(static_cast<expr*>(nodes[nodes.size()-2]), static_cast<expr*>(nodes[nodes.size()-1]))); // binary app
        nodes.push_back(m.mk_and(static_cast<expr*>(nodes[nodes.size()-1]), m.mk_true())); // binary app with builtin
    }

    double end_time = get_time_seconds();
    double elapsed = end_time - start_time;

    std::cout << "Created " << nodes.size() << " mixed AST nodes in " << elapsed << " seconds\n";
    std::cout << "Rate: " << (nodes.size() / elapsed) << " allocations/sec\n";
    std::cout << "Average time per allocation: " << (elapsed * 1000000.0 / nodes.size()) << " microseconds\n";

    std::cout << "Total allocated size: " << m.get_allocation_size() << " bytes\n";
}

void benchmark_allocation_deallocation_pattern(ast_manager& m, unsigned num_iterations) {
    std::cout << "\nBenchmarking allocation/deallocation pattern (" << num_iterations << " iterations)...\n";

    sort* int_sort = m.mk_int_sort();

    double start_time = get_time_seconds();

    // Simulate a pattern of creating and releasing AST nodes
    for (unsigned i = 0; i < num_iterations; ++i) {
        {
            // Create a temporary scope with many AST nodes
            std::vector<expr_ref> temp_exprs(m);
            for (unsigned j = 0; j < 20; ++j) {
                temp_exprs.push_back(m.mk_const(symbol((std::to_string(i) + "_" + std::to_string(j)).c_str()), int_sort));
            }

            // Create some applications using these
            for (unsigned j = 0; j < 10; ++j) {
                temp_exprs.push_back(m.mk_eq(temp_exprs[j], temp_exprs[j + 10]));
            }
        } // All expr_refs go out of scope here, potentially triggering deallocation
    }

    double end_time = get_time_seconds();
    double elapsed = end_time - start_time;

    std::cout << "Completed allocation/deallocation pattern in " << elapsed << " seconds\n";
    std::cout << "Rate: " << (num_iterations / elapsed) << " cycles/sec\n";
    std::cout << "Final allocated size: " << m.get_allocation_size() << " bytes\n";
}

int main() {
    std::cout << "=== AST Allocation Performance Benchmark ===\n";

    // Create ast_manager for testing
    ast_manager m;

    // Run different benchmark scenarios
    unsigned iterations = 50000;  // Adjust based on desired test duration

    benchmark_app_allocation(m, iterations);
    benchmark_mixed_allocation(m, iterations);
    benchmark_allocation_deallocation_pattern(m, iterations / 10); // Less iterations for this one

    // Report final memory statistics
    std::cout << "\n=== Final Memory Statistics ===\n";
    std::cout << "Total memory allocated: " << m.get_allocation_size() << " bytes\n";
    std::cout << "AST table size: " << m.get_num_asts() << " nodes\n";

    return 0;
}