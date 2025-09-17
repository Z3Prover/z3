#include <iostream>
#include <chrono>
#include <thread>
#include <vector>
#include <atomic>
#include <random>
#include <mutex>
#include <queue>

/**
 * Simplified performance test to measure lock contention in parallel operations
 * This simulates the Z3 parallel SAT solver bottlenecks without full Z3 dependencies
 */

using namespace std;
using namespace std::chrono;

// Simulate the current mutex-based approach
class MutexBasedExchange {
private:
    mutex m_mutex;
    vector<int> m_shared_data;

public:
    void exchange_operation(const vector<int>& input, vector<int>& output) {
        lock_guard<mutex> lock(m_mutex);

        // Simulate the work done in Z3's unit exchange
        for (int val : input) {
            m_shared_data.push_back(val);
        }

        // Simulate reading shared data
        output.clear();
        if (m_shared_data.size() > 10) {
            output.assign(m_shared_data.end() - 10, m_shared_data.end());
        }
    }
};

// Lock-free approach using atomic operations and per-thread queues
class LockFreeExchange {
private:
    static constexpr size_t NUM_THREADS = 4;
    atomic<size_t> m_write_index{0};
    vector<int> m_shared_buffer;
    atomic<size_t> m_read_indices[NUM_THREADS];

public:
    LockFreeExchange() : m_shared_buffer(100000) {
        for (size_t i = 0; i < NUM_THREADS; ++i) {
            m_read_indices[i].store(0);
        }
    }

    void exchange_operation(size_t thread_id, const vector<int>& input, vector<int>& output) {
        // Lock-free write using atomic increment
        for (int val : input) {
            size_t write_pos = m_write_index.fetch_add(1) % m_shared_buffer.size();
            m_shared_buffer[write_pos] = val;
        }

        // Lock-free read
        output.clear();
        size_t current_write = m_write_index.load();
        size_t read_pos = m_read_indices[thread_id].load();

        // Read up to 10 new values
        for (int i = 0; i < 10 && read_pos != current_write; ++i) {
            output.push_back(m_shared_buffer[read_pos % m_shared_buffer.size()]);
            read_pos++;
        }

        m_read_indices[thread_id].store(read_pos);
    }
};

class PerformanceTest {
private:
    static constexpr unsigned NUM_THREADS = 4;
    static constexpr unsigned NUM_OPERATIONS = 50000;
    static constexpr unsigned INPUT_SIZE = 10;

public:
    struct Result {
        double mutex_time_ms;
        double lockfree_time_ms;
        double speedup_factor;
    };

    Result run_comparison_test() {
        cout << "Running parallel performance comparison..." << endl;

        Result result;

        // Test mutex-based approach
        result.mutex_time_ms = test_mutex_approach();

        // Test lock-free approach
        result.lockfree_time_ms = test_lockfree_approach();

        result.speedup_factor = result.mutex_time_ms / result.lockfree_time_ms;

        return result;
    }

private:
    double test_mutex_approach() {
        cout << "Testing mutex-based approach..." << endl;

        MutexBasedExchange exchange;
        atomic<bool> start_flag{false};
        vector<thread> threads;

        auto start_time = high_resolution_clock::now();

        // Launch worker threads
        for (unsigned t = 0; t < NUM_THREADS; ++t) {
            threads.emplace_back([&, t]() {
                while (!start_flag.load()) {
                    this_thread::yield();
                }

                random_device rd;
                mt19937 gen(rd() + t);
                uniform_int_distribution<> dis(1, 1000);

                for (unsigned op = 0; op < NUM_OPERATIONS; ++op) {
                    vector<int> input(INPUT_SIZE), output;
                    for (int& val : input) {
                        val = dis(gen);
                    }

                    exchange.exchange_operation(input, output);
                }
            });
        }

        // Start all threads
        start_flag.store(true);

        // Wait for completion
        for (auto& t : threads) {
            t.join();
        }

        auto end_time = high_resolution_clock::now();
        double elapsed_ms = duration<double, milli>(end_time - start_time).count();

        cout << "Mutex approach completed in " << elapsed_ms << "ms" << endl;
        return elapsed_ms;
    }

    double test_lockfree_approach() {
        cout << "Testing lock-free approach..." << endl;

        LockFreeExchange exchange;
        atomic<bool> start_flag{false};
        vector<thread> threads;

        auto start_time = high_resolution_clock::now();

        // Launch worker threads
        for (unsigned t = 0; t < NUM_THREADS; ++t) {
            threads.emplace_back([&, t]() {
                while (!start_flag.load()) {
                    this_thread::yield();
                }

                random_device rd;
                mt19937 gen(rd() + t);
                uniform_int_distribution<> dis(1, 1000);

                for (unsigned op = 0; op < NUM_OPERATIONS; ++op) {
                    vector<int> input(INPUT_SIZE), output;
                    for (int& val : input) {
                        val = dis(gen);
                    }

                    exchange.exchange_operation(t, input, output);
                }
            });
        }

        // Start all threads
        start_flag.store(true);

        // Wait for completion
        for (auto& t : threads) {
            t.join();
        }

        auto end_time = high_resolution_clock::now();
        double elapsed_ms = duration<double, milli>(end_time - start_time).count();

        cout << "Lock-free approach completed in " << elapsed_ms << "ms" << endl;
        return elapsed_ms;
    }
};

int main() {
    cout << "=== Lock-Free Parallel Algorithm Performance Test ===" << endl;

    PerformanceTest test;
    auto result = test.run_comparison_test();

    cout << "\n=== Performance Results ===" << endl;
    cout << "Mutex-based time: " << result.mutex_time_ms << " ms" << endl;
    cout << "Lock-free time: " << result.lockfree_time_ms << " ms" << endl;
    cout << "Speedup factor: " << result.speedup_factor << "x" << endl;

    if (result.speedup_factor > 1.0) {
        cout << "✅ Lock-free approach is " << result.speedup_factor << "x faster!" << endl;
    } else {
        cout << "⚠️  Lock-free approach is slower - needs optimization" << endl;
    }

    return 0;
}