#include <iostream>
#include <chrono>
#include <vector>
#include <thread>
#include <atomic>
#include <random>
#include "sat/sat_parallel.h"
#include "sat/sat_solver.h"

using namespace std;
using namespace sat;

/**
 * Performance test for Z3 parallel SAT solving operations
 * Tests the current mutex-based approach to establish baseline
 */
class ParallelPerformanceTest {
private:
    static constexpr unsigned NUM_THREADS = 4;
    static constexpr unsigned NUM_OPERATIONS = 10000;
    static constexpr unsigned NUM_LITERALS_PER_OP = 50;

public:
    struct TestResult {
        double unit_exchange_time_ms;
        double clause_sharing_time_ms;
        unsigned total_operations;
    };

    TestResult run_baseline_test() {
        TestResult result = {0.0, 0.0, 0};

        // Create basic solver setup for testing
        params_ref p;
        reslimit rl;
        solver s(p, rl);

        // Create parallel coordinator
        parallel par(s);
        par.init_solvers(s, NUM_THREADS - 1);

        cout << "Running baseline performance test with " << NUM_THREADS << " threads..." << endl;

        // Test unit literal exchange performance
        result.unit_exchange_time_ms = test_unit_exchange(par, s);

        // Test clause sharing performance
        result.clause_sharing_time_ms = test_clause_sharing(par, s);

        result.total_operations = NUM_OPERATIONS * NUM_THREADS;

        return result;
    }

private:
    double test_unit_exchange(parallel& par, solver& s) {
        cout << "Testing unit literal exchange..." << endl;

        atomic<bool> start_flag{false};
        atomic<unsigned> completed_ops{0};
        vector<thread> threads;

        auto start_time = chrono::high_resolution_clock::now();

        // Launch threads that perform unit exchange operations
        for (unsigned t = 0; t < NUM_THREADS; ++t) {
            threads.emplace_back([&, t]() {
                // Wait for start signal
                while (!start_flag.load()) {
                    this_thread::yield();
                }

                // Perform unit exchange operations
                literal_vector in_literals, out_literals;
                unsigned limit = 0;
                random_device rd;
                mt19937 gen(rd() + t);
                uniform_int_distribution<> dis(1, 1000);

                for (unsigned i = 0; i < NUM_OPERATIONS; ++i) {
                    // Generate random literals for exchange
                    in_literals.clear();
                    for (unsigned j = 0; j < NUM_LITERALS_PER_OP; ++j) {
                        bool_var var = static_cast<bool_var>(dis(gen));
                        literal lit(var, j % 2 == 0);
                        in_literals.push_back(lit);
                    }

                    out_literals.clear();

                    // This is the bottleneck we're testing - unit exchange with global mutex
                    par.exchange(par.get_solver(t % (NUM_THREADS-1)), in_literals, limit, out_literals);

                    completed_ops.fetch_add(1);
                }
            });
        }

        // Start all threads simultaneously
        start_flag.store(true);

        // Wait for completion
        for (auto& t : threads) {
            t.join();
        }

        auto end_time = chrono::high_resolution_clock::now();
        double elapsed_ms = chrono::duration<double, milli>(end_time - start_time).count();

        cout << "Unit exchange completed: " << completed_ops.load() << " operations in "
             << elapsed_ms << "ms" << endl;

        return elapsed_ms;
    }

    double test_clause_sharing(parallel& par, solver& s) {
        cout << "Testing clause sharing..." << endl;

        atomic<bool> start_flag{false};
        atomic<unsigned> completed_ops{0};
        vector<thread> threads;

        auto start_time = chrono::high_resolution_clock::now();

        // Launch threads that perform clause sharing operations
        for (unsigned t = 0; t < NUM_THREADS; ++t) {
            threads.emplace_back([&, t]() {
                // Wait for start signal
                while (!start_flag.load()) {
                    this_thread::yield();
                }

                random_device rd;
                mt19937 gen(rd() + t);
                uniform_int_distribution<> dis(1, 100);

                for (unsigned i = 0; i < NUM_OPERATIONS / 2; ++i) { // Fewer clause ops
                    // Generate random binary clauses for sharing
                    bool_var var1 = static_cast<bool_var>(dis(gen));
                    bool_var var2 = static_cast<bool_var>(dis(gen));
                    literal l1(var1, i % 2 == 0);
                    literal l2(var2, i % 3 == 0);

                    // This is the bottleneck we're testing - clause sharing with global mutex
                    par.share_clause(par.get_solver(t % (NUM_THREADS-1)), l1, l2);

                    completed_ops.fetch_add(1);
                }
            });
        }

        // Start all threads simultaneously
        start_flag.store(true);

        // Wait for completion
        for (auto& t : threads) {
            t.join();
        }

        auto end_time = chrono::high_resolution_clock::now();
        double elapsed_ms = chrono::duration<double, milli>(end_time - start_time).count();

        cout << "Clause sharing completed: " << completed_ops.load() << " operations in "
             << elapsed_ms << "ms" << endl;

        return elapsed_ms;
    }
};

int main() {
    cout << "=== Z3 Parallel SAT Solver Performance Test ===" << endl;
    cout << "Testing current mutex-based synchronization baseline..." << endl;

    ParallelPerformanceTest test;
    auto result = test.run_baseline_test();

    cout << "\n=== Baseline Performance Results ===" << endl;
    cout << "Unit Exchange Time: " << result.unit_exchange_time_ms << " ms" << endl;
    cout << "Clause Sharing Time: " << result.clause_sharing_time_ms << " ms" << endl;
    cout << "Total Operations: " << result.total_operations << endl;
    cout << "Unit Exchange Throughput: " << (result.total_operations / result.unit_exchange_time_ms * 1000) << " ops/sec" << endl;
    cout << "Clause Sharing Throughput: " << ((result.total_operations/2) / result.clause_sharing_time_ms * 1000) << " ops/sec" << endl;

    return 0;
}