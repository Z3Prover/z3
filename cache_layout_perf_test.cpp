#include <iostream>
#include <vector>
#include <chrono>
#include <cstring>
#include <random>
#include <immintrin.h>

// Simple performance benchmark for cache-friendly data access patterns
// This will help us measure the impact of our optimizations

struct alignas(64) VariableData {
    // Cache-aligned structure for variable-related data
    unsigned activity;
    bool phase;
    bool best_phase;
    bool decision;
    bool mark;
    bool eliminated;
    bool external;
    uint64_t last_conflict;
    uint64_t last_propagation;
    uint64_t participated;
    uint64_t canceled;
    uint64_t reasoned;
    unsigned touch_count;
    unsigned scope;
    char assigned_since_gc;
    // Padding to fill cache line (64 bytes)
    char padding[64 - (sizeof(unsigned) + 5*sizeof(bool) + 5*sizeof(uint64_t) + 2*sizeof(unsigned) + sizeof(char))];
};

class CacheFriendlyDataLayout {
private:
    std::vector<VariableData> m_var_data;
    size_t m_num_vars;

public:
    CacheFriendlyDataLayout(size_t num_vars) : m_num_vars(num_vars) {
        m_var_data.resize(num_vars);

        // Initialize with random data
        std::random_device rd;
        std::mt19937 gen(rd());
        std::uniform_int_distribution<> dis(0, 1000);

        for (auto& data : m_var_data) {
            data.activity = dis(gen);
            data.phase = dis(gen) % 2;
            data.best_phase = dis(gen) % 2;
            data.decision = dis(gen) % 2;
            data.last_conflict = dis(gen);
            data.last_propagation = dis(gen);
        }
    }

    // Simulate typical SAT solver variable access patterns
    void simulate_variable_selection(size_t iterations) {
        size_t max_activity = 0;
        size_t best_var = 0;

        for (size_t iter = 0; iter < iterations; ++iter) {
            max_activity = 0;
            best_var = 0;

            // Simulate VSIDS variable selection - access all variables
            for (size_t var = 0; var < m_num_vars; ++var) {
                // Add prefetch hint for next cache line
                if (var + 1 < m_num_vars) {
                    __builtin_prefetch(&m_var_data[var + 1], 0, 3);
                }

                auto& data = m_var_data[var];

                // Typical variable selection logic
                if (!data.eliminated && !data.mark && data.activity > max_activity) {
                    max_activity = data.activity;
                    best_var = var;
                }

                // Update activity (simulating conflict analysis)
                if (data.last_conflict > data.last_propagation) {
                    data.activity++;
                }
            }

            // Update selected variable data
            if (best_var < m_num_vars) {
                auto& selected = m_var_data[best_var];
                selected.decision = true;
                selected.touch_count++;
                selected.last_propagation = iter;
            }
        }

        // Prevent compiler optimization
        volatile size_t result = best_var;
        (void)result;
    }

    void simulate_propagation_access(size_t iterations) {
        for (size_t iter = 0; iter < iterations; ++iter) {
            // Simulate propagation - scattered access pattern
            for (size_t i = 0; i < std::min(m_num_vars, 1000ul); ++i) {
                size_t var_idx = (iter * 7 + i * 13) % m_num_vars;

                // Prefetch next likely access
                size_t next_var = (var_idx + 17) % m_num_vars;
                __builtin_prefetch(&m_var_data[next_var], 0, 3);

                auto& data = m_var_data[var_idx];

                // Typical propagation updates
                data.last_propagation = iter;
                data.participated++;

                // Phase saving
                if (iter % 100 == 0) {
                    data.best_phase = data.phase;
                }
            }
        }
    }
};

// Baseline implementation - separate vectors (current Z3 approach)
class BaselineDataLayout {
private:
    std::vector<unsigned> m_activity;
    std::vector<bool> m_phase;
    std::vector<bool> m_best_phase;
    std::vector<bool> m_decision;
    std::vector<bool> m_mark;
    std::vector<bool> m_eliminated;
    std::vector<uint64_t> m_last_conflict;
    std::vector<uint64_t> m_last_propagation;
    std::vector<uint64_t> m_participated;
    std::vector<unsigned> m_touch_count;
    size_t m_num_vars;

public:
    BaselineDataLayout(size_t num_vars) : m_num_vars(num_vars) {
        m_activity.resize(num_vars);
        m_phase.resize(num_vars);
        m_best_phase.resize(num_vars);
        m_decision.resize(num_vars);
        m_mark.resize(num_vars);
        m_eliminated.resize(num_vars);
        m_last_conflict.resize(num_vars);
        m_last_propagation.resize(num_vars);
        m_participated.resize(num_vars);
        m_touch_count.resize(num_vars);

        // Initialize with random data
        std::random_device rd;
        std::mt19937 gen(rd());
        std::uniform_int_distribution<> dis(0, 1000);

        for (size_t i = 0; i < num_vars; ++i) {
            m_activity[i] = dis(gen);
            m_phase[i] = dis(gen) % 2;
            m_best_phase[i] = dis(gen) % 2;
            m_decision[i] = dis(gen) % 2;
            m_last_conflict[i] = dis(gen);
            m_last_propagation[i] = dis(gen);
        }
    }

    void simulate_variable_selection(size_t iterations) {
        size_t max_activity = 0;
        size_t best_var = 0;

        for (size_t iter = 0; iter < iterations; ++iter) {
            max_activity = 0;
            best_var = 0;

            // Simulate VSIDS variable selection
            for (size_t var = 0; var < m_num_vars; ++var) {
                if (!m_eliminated[var] && !m_mark[var] && m_activity[var] > max_activity) {
                    max_activity = m_activity[var];
                    best_var = var;
                }

                if (m_last_conflict[var] > m_last_propagation[var]) {
                    m_activity[var]++;
                }
            }

            if (best_var < m_num_vars) {
                m_decision[best_var] = true;
                m_touch_count[best_var]++;
                m_last_propagation[best_var] = iter;
            }
        }

        volatile size_t result = best_var;
        (void)result;
    }

    void simulate_propagation_access(size_t iterations) {
        for (size_t iter = 0; iter < iterations; ++iter) {
            for (size_t i = 0; i < std::min(m_num_vars, 1000ul); ++i) {
                size_t var_idx = (iter * 7 + i * 13) % m_num_vars;

                m_last_propagation[var_idx] = iter;
                m_participated[var_idx]++;

                if (iter % 100 == 0) {
                    m_best_phase[var_idx] = m_phase[var_idx];
                }
            }
        }
    }
};

double benchmark_layout(const std::string& name, auto& layout, size_t iterations) {
    auto start = std::chrono::high_resolution_clock::now();

    layout.simulate_variable_selection(iterations / 2);
    layout.simulate_propagation_access(iterations / 2);

    auto end = std::chrono::high_resolution_clock::now();
    auto duration = std::chrono::duration_cast<std::chrono::microseconds>(end - start);

    std::cout << name << " layout: " << duration.count() << " μs" << std::endl;
    return duration.count();
}

int main() {
    const size_t num_vars = 100000;
    const size_t iterations = 1000;

    std::cout << "Cache-Friendly Data Layout Performance Benchmark\n";
    std::cout << "Variables: " << num_vars << ", Iterations: " << iterations << "\n\n";

    // Test baseline implementation
    BaselineDataLayout baseline(num_vars);
    double baseline_time = benchmark_layout("Baseline", baseline, iterations);

    // Test cache-friendly implementation
    CacheFriendlyDataLayout optimized(num_vars);
    double optimized_time = benchmark_layout("Cache-friendly", optimized, iterations);

    // Calculate improvement
    double improvement = (baseline_time - optimized_time) / baseline_time * 100.0;
    double speedup = baseline_time / optimized_time;

    std::cout << "\n=== Performance Results ===\n";
    std::cout << "Baseline time: " << baseline_time << " μs\n";
    std::cout << "Optimized time: " << optimized_time << " μs\n";
    std::cout << "Improvement: " << improvement << "%\n";
    std::cout << "Speedup: " << speedup << "x\n";

    // Memory layout information
    std::cout << "\n=== Memory Layout Information ===\n";
    std::cout << "VariableData size: " << sizeof(VariableData) << " bytes\n";
    std::cout << "VariableData alignment: " << alignof(VariableData) << " bytes\n";
    std::cout << "Cache line size: 64 bytes\n";

    return 0;
}