#include <iostream>
#include <chrono>
#include <thread>
#include <vector>
#include <atomic>
#include <random>
#include <fstream>
#include <mutex>

/**
 * Performance benchmark to measure fine-grained locking improvements
 * in Z3 parallel SAT solver operations
 */

using namespace std;
using namespace std::chrono;

// Simulate parallel operations with different locking strategies
class LockingBenchmark {
public:
    static constexpr size_t NUM_THREADS = 4;
    static constexpr size_t NUM_OPS_PER_THREAD = 25000;
    static constexpr size_t WORK_SIZE = 20;
    struct BenchmarkResult {
        double coarse_grained_ms;
        double fine_grained_ms;
        double speedup_factor;
        size_t total_operations;
    };

    BenchmarkResult run_comparison() {
        cout << "=== Z3 Parallel SAT Solver Locking Benchmark ===" << endl;
        cout << "Testing " << NUM_THREADS << " threads, "
             << NUM_OPS_PER_THREAD << " ops/thread" << endl;

        BenchmarkResult result;
        result.total_operations = NUM_THREADS * NUM_OPS_PER_THREAD;

        // Test coarse-grained locking (original approach)
        result.coarse_grained_ms = test_coarse_grained_locking();

        // Test fine-grained locking (optimized approach)
        result.fine_grained_ms = test_fine_grained_locking();

        result.speedup_factor = result.coarse_grained_ms / result.fine_grained_ms;

        return result;
    }

private:
    // Simulate original Z3 approach with single global mutex
    double test_coarse_grained_locking() {
        cout << "Testing coarse-grained locking (single mutex)..." << endl;

        mutex global_mutex;
        vector<int> shared_unit_data, shared_clause_data;
        atomic<bool> start_flag{false};
        vector<thread> threads;

        auto start_time = high_resolution_clock::now();

        for (size_t t = 0; t < NUM_THREADS; ++t) {
            threads.emplace_back([&, t]() {
                while (!start_flag.load()) {
                    this_thread::yield();
                }

                random_device rd;
                mt19937 gen(rd() + t);
                uniform_int_distribution<> dis(1, 1000);

                for (size_t op = 0; op < NUM_OPS_PER_THREAD; ++op) {
                    // Simulate unit literal exchange
                    {
                        lock_guard<mutex> lock(global_mutex);
                        for (size_t i = 0; i < WORK_SIZE / 4; ++i) {
                            shared_unit_data.push_back(dis(gen));
                        }
                        // Simulate reading shared data
                        volatile int sum = 0;
                        for (size_t i = 0; i < min(size_t(10), shared_unit_data.size()); ++i) {
                            sum += shared_unit_data[i];
                        }
                    }

                    // Simulate clause sharing
                    {
                        lock_guard<mutex> lock(global_mutex);
                        for (size_t i = 0; i < WORK_SIZE / 2; ++i) {
                            shared_clause_data.push_back(dis(gen));
                        }
                    }
                }
            });
        }

        start_flag.store(true);
        for (auto& t : threads) {
            t.join();
        }

        auto end_time = high_resolution_clock::now();
        double elapsed_ms = duration<double, milli>(end_time - start_time).count();

        cout << "Coarse-grained completed in " << elapsed_ms << "ms" << endl;
        return elapsed_ms;
    }

    // Simulate optimized Z3 approach with separate mutexes
    double test_fine_grained_locking() {
        cout << "Testing fine-grained locking (separate mutexes)..." << endl;

        mutex unit_mutex, clause_mutex;
        vector<int> shared_unit_data, shared_clause_data;
        atomic<bool> start_flag{false};
        vector<thread> threads;

        auto start_time = high_resolution_clock::now();

        for (size_t t = 0; t < NUM_THREADS; ++t) {
            threads.emplace_back([&, t]() {
                while (!start_flag.load()) {
                    this_thread::yield();
                }

                random_device rd;
                mt19937 gen(rd() + t);
                uniform_int_distribution<> dis(1, 1000);

                for (size_t op = 0; op < NUM_OPS_PER_THREAD; ++op) {
                    // Pre-compute work outside critical sections
                    vector<int> unit_work, clause_work;
                    unit_work.reserve(WORK_SIZE / 4);
                    clause_work.reserve(WORK_SIZE / 2);

                    for (size_t i = 0; i < WORK_SIZE / 4; ++i) {
                        unit_work.push_back(dis(gen));
                    }
                    for (size_t i = 0; i < WORK_SIZE / 2; ++i) {
                        clause_work.push_back(dis(gen));
                    }

                    // Separate critical sections with prefetch
                    {
                        lock_guard<mutex> lock(unit_mutex);
                        __builtin_prefetch(shared_unit_data.data(), 1, 3);
                        shared_unit_data.insert(shared_unit_data.end(),
                                               unit_work.begin(), unit_work.end());

                        // Simulate reading shared data
                        volatile int sum = 0;
                        for (size_t i = 0; i < min(size_t(10), shared_unit_data.size()); ++i) {
                            sum += shared_unit_data[i];
                        }
                    }

                    {
                        lock_guard<mutex> lock(clause_mutex);
                        __builtin_prefetch(shared_clause_data.data(), 1, 3);
                        shared_clause_data.insert(shared_clause_data.end(),
                                                 clause_work.begin(), clause_work.end());
                    }
                }
            });
        }

        start_flag.store(true);
        for (auto& t : threads) {
            t.join();
        }

        auto end_time = high_resolution_clock::now();
        double elapsed_ms = duration<double, milli>(end_time - start_time).count();

        cout << "Fine-grained completed in " << elapsed_ms << "ms" << endl;
        return elapsed_ms;
    }
};

int main() {
    LockingBenchmark benchmark;
    auto result = benchmark.run_comparison();

    cout << "\n=== Parallel Algorithm Improvement Results ===" << endl;
    cout << "Total operations: " << result.total_operations << endl;
    cout << "Coarse-grained time: " << result.coarse_grained_ms << " ms" << endl;
    cout << "Fine-grained time: " << result.fine_grained_ms << " ms" << endl;
    cout << "Speedup factor: " << result.speedup_factor << "x" << endl;

    if (result.speedup_factor > 1.0) {
        cout << "✅ Fine-grained locking is " << result.speedup_factor << "x faster!" << endl;
        cout << "Performance improvement: " << ((result.speedup_factor - 1.0) * 100.0) << "%" << endl;
    } else {
        cout << "⚠️  Fine-grained approach needs further optimization" << endl;
    }

    // Calculate throughput
    double coarse_throughput = result.total_operations / (result.coarse_grained_ms / 1000.0);
    double fine_throughput = result.total_operations / (result.fine_grained_ms / 1000.0);

    cout << "\nThroughput Analysis:" << endl;
    cout << "Coarse-grained: " << static_cast<int>(coarse_throughput) << " ops/sec" << endl;
    cout << "Fine-grained: " << static_cast<int>(fine_throughput) << " ops/sec" << endl;

    // Write results to file for analysis
    ofstream results_file("parallel_benchmark_results.txt");
    results_file << "Parallel Algorithm Improvement Benchmark Results\n";
    results_file << "==============================================\n\n";
    results_file << "Configuration:\n";
    results_file << "- Threads: " << LockingBenchmark::NUM_THREADS << "\n";
    results_file << "- Operations per thread: " << LockingBenchmark::NUM_OPS_PER_THREAD << "\n";
    results_file << "- Total operations: " << result.total_operations << "\n\n";
    results_file << "Results:\n";
    results_file << "- Coarse-grained time: " << result.coarse_grained_ms << " ms\n";
    results_file << "- Fine-grained time: " << result.fine_grained_ms << " ms\n";
    results_file << "- Speedup factor: " << result.speedup_factor << "x\n";
    results_file << "- Performance improvement: " << ((result.speedup_factor - 1.0) * 100.0) << "%\n";
    results_file << "- Coarse-grained throughput: " << static_cast<int>(coarse_throughput) << " ops/sec\n";
    results_file << "- Fine-grained throughput: " << static_cast<int>(fine_throughput) << " ops/sec\n";
    results_file.close();

    cout << "\nResults written to parallel_benchmark_results.txt" << endl;

    return 0;
}