#include "util/heap.h"
#include "util/timeit.h"
#include "util/stopwatch.h"
#include <vector>
#include <random>
#include <iostream>
#include <chrono>
#include <numeric>
#include <algorithm>

// Test activity vector for heap operations
using activity_vector = std::vector<unsigned>;

struct activity_less_than {
    const activity_vector& m_activity;
    activity_less_than(const activity_vector& act) : m_activity(act) {}
    bool operator()(int v1, int v2) const { return m_activity[v1] > m_activity[v2]; }
};

class heap_performance_test {
private:
    static constexpr unsigned NUM_VARIABLES = 10000;
    static constexpr unsigned NUM_OPERATIONS = 100000;

    activity_vector m_activity;
    std::mt19937 m_rng{42}; // Fixed seed for reproducible results

    void setup() {
        m_activity.resize(NUM_VARIABLES);

        // Initialize with random activities
        std::uniform_int_distribution<unsigned> dist(1, 1000000);
        for (unsigned i = 0; i < NUM_VARIABLES; ++i) {
            m_activity[i] = dist(m_rng);
        }
    }

public:

    void test_heap_operations() {
        std::cout << "=== VSIDS Heap Performance Test ===\n";

        setup();

        // Test individual insertions (baseline)
        {
            heap<activity_less_than> h(NUM_VARIABLES, activity_less_than(m_activity));
            stopwatch timer;
            timer.start();

            for (unsigned i = 0; i < NUM_VARIABLES; ++i) {
                h.insert(i);
            }

            timer.stop();
            std::cout << "Individual insertions: " << timer.get_seconds() << "s\n";
        }

        // Test heap operations under heavy load
        {
            heap<activity_less_than> h(NUM_VARIABLES, activity_less_than(m_activity));

            // Insert all variables
            for (unsigned i = 0; i < NUM_VARIABLES; ++i) {
                h.insert(i);
            }

            stopwatch timer;
            timer.start();

            std::uniform_int_distribution<unsigned> var_dist(0, NUM_VARIABLES - 1);
            std::uniform_int_distribution<int> op_dist(0, 2);

            for (unsigned op = 0; op < NUM_OPERATIONS; ++op) {
                unsigned var = var_dist(m_rng);
                int operation = op_dist(m_rng);

                switch (operation) {
                case 0: // Activity increase
                    m_activity[var] += 100;
                    if (h.contains(var)) {
                        h.decreased(var); // Higher activity = higher priority
                    }
                    break;

                case 1: // Extract minimum
                    if (!h.empty()) {
                        unsigned min_var = h.erase_min();
                        // Re-insert to keep heap populated
                        h.insert(min_var);
                    }
                    break;

                case 2: // Activity decrease
                    if (m_activity[var] > 100) {
                        m_activity[var] -= 100;
                        if (h.contains(var)) {
                            h.increased(var); // Lower activity = lower priority
                        }
                    }
                    break;
                }
            }

            timer.stop();
            std::cout << "Mixed operations (" << NUM_OPERATIONS << "): " << timer.get_seconds() << "s\n";
            std::cout << "Operations per second: " << (NUM_OPERATIONS / timer.get_seconds()) << "\n";
        }

        // Test activity rescaling performance
        {
            activity_vector activities(NUM_VARIABLES);
            std::iota(activities.begin(), activities.end(), 1);

            stopwatch timer;
            timer.start();

            // Simulate rescaling like in the SAT solver
            constexpr unsigned NUM_RESCALES = 1000;
            for (unsigned r = 0; r < NUM_RESCALES; ++r) {
                // Test our optimized rescaling approach
                const unsigned size = activities.size();
                unsigned* data = activities.data();
                const unsigned chunk_size = 4;
                unsigned i = 0;

                // SIMD-friendly chunked processing
                for (; i + chunk_size <= size; i += chunk_size) {
                    data[i] >>= 1;
                    data[i + 1] >>= 1;
                    data[i + 2] >>= 1;
                    data[i + 3] >>= 1;
                }

                // Handle remainder
                for (; i < size; ++i) {
                    data[i] >>= 1;
                }
            }

            timer.stop();
            std::cout << "Activity rescaling (" << NUM_RESCALES << " rescales): " << timer.get_seconds() << "s\n";
        }
    }

    void test_cache_locality() {
        std::cout << "\n=== Cache Locality Test ===\n";

        setup();
        heap<activity_less_than> h(NUM_VARIABLES, activity_less_than(m_activity));

        // Fill heap
        for (unsigned i = 0; i < NUM_VARIABLES; ++i) {
            h.insert(i);
        }

        // Test sequential access pattern (good cache behavior)
        {
            stopwatch timer;
            timer.start();

            for (unsigned round = 0; round < 100; ++round) {
                for (unsigned i = 0; i < NUM_VARIABLES; ++i) {
                    if (h.contains(i)) {
                        m_activity[i]++; // Touch activity array sequentially
                    }
                }
            }

            timer.stop();
            std::cout << "Sequential access: " << timer.get_seconds() << "s\n";
        }

        // Test random access pattern (poor cache behavior)
        {
            std::vector<unsigned> random_indices(NUM_VARIABLES);
            std::iota(random_indices.begin(), random_indices.end(), 0);
            std::shuffle(random_indices.begin(), random_indices.end(), m_rng);

            stopwatch timer;
            timer.start();

            for (unsigned round = 0; round < 100; ++round) {
                for (unsigned i : random_indices) {
                    if (h.contains(i)) {
                        m_activity[i]++; // Touch activity array randomly
                    }
                }
            }

            timer.stop();
            std::cout << "Random access: " << timer.get_seconds() << "s\n";
        }
    }
};

int main() {
    heap_performance_test test;

    try {
        test.test_heap_operations();
        test.test_cache_locality();

        std::cout << "\n=== Performance Test Complete ===\n";
        std::cout << "Optimizations implemented:\n";
        std::cout << "- Cache prefetch hints in heap operations\n";
        std::cout << "- Chunked activity rescaling\n";
        std::cout << "- Bulk insertion method\n";
        std::cout << "- Memory access pattern improvements\n";

    } catch (const std::exception& e) {
        std::cerr << "Error: " << e.what() << std::endl;
        return 1;
    }

    return 0;
}