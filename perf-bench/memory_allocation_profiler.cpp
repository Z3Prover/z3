/*++
Copyright (c) 2025 Microsoft Corporation

Module Name:

    memory_allocation_profiler.cpp

Abstract:

    Memory allocation profiler for Z3 components.
    This tool helps identify memory allocation patterns and bottlenecks
    in Z3's core components, specifically targeting the areas mentioned
    by maintainers as performance bottlenecks.

Author:

    Daily Perf Improver 2025-01-17.

--*/

#include <iostream>
#include <unordered_map>
#include <vector>
#include <string>
#include <chrono>
#include <algorithm>
#include <iomanip>
#include <fstream>
#include <memory>
#include <cstdlib>
#include <cstring>

#ifdef __GNUC__
#include <execinfo.h>
#include <cxxabi.h>
#include <dlfcn.h>
#endif

/**
 * Simple allocation tracker for profiling Z3's memory usage patterns
 */
class AllocationProfiler {
private:
    struct AllocationInfo {
        size_t size;
        std::chrono::high_resolution_clock::time_point timestamp;
        std::string location; // For stack trace or hint
        size_t count = 1; // Number of allocations of this size
    };

    struct AllocationStats {
        size_t total_size = 0;
        size_t total_count = 0;
        size_t peak_size = 0;
        std::chrono::high_resolution_clock::time_point first_alloc;
        std::chrono::high_resolution_clock::time_point last_alloc;
        std::vector<size_t> size_histogram;
    };

    std::unordered_map<void*, AllocationInfo> allocations;
    std::unordered_map<size_t, AllocationStats> size_stats; // Group by allocation size
    std::unordered_map<std::string, AllocationStats> location_stats; // Group by location

    size_t current_memory_usage = 0;
    size_t peak_memory_usage = 0;
    size_t total_allocations = 0;
    size_t total_deallocations = 0;

    bool enabled = true;

public:
    void record_allocation(void* ptr, size_t size, const std::string& location = "") {
        if (!enabled || !ptr) return;

        auto now = std::chrono::high_resolution_clock::now();

        allocations[ptr] = {size, now, location};

        current_memory_usage += size;
        peak_memory_usage = std::max(peak_memory_usage, current_memory_usage);
        total_allocations++;

        // Update size statistics
        auto& size_stat = size_stats[size];
        size_stat.total_size += size;
        size_stat.total_count++;
        size_stat.peak_size = std::max(size_stat.peak_size, size);
        if (size_stat.total_count == 1) {
            size_stat.first_alloc = now;
        }
        size_stat.last_alloc = now;

        // Update location statistics
        if (!location.empty()) {
            auto& loc_stat = location_stats[location];
            loc_stat.total_size += size;
            loc_stat.total_count++;
            loc_stat.peak_size = std::max(loc_stat.peak_size, size);
            if (loc_stat.total_count == 1) {
                loc_stat.first_alloc = now;
            }
            loc_stat.last_alloc = now;
        }
    }

    void record_deallocation(void* ptr) {
        if (!enabled || !ptr) return;

        auto it = allocations.find(ptr);
        if (it != allocations.end()) {
            current_memory_usage -= it->second.size;
            total_deallocations++;
            allocations.erase(it);
        }
    }

    void print_summary() const {
        std::cout << "\n=== Memory Allocation Profile Summary ===" << std::endl;
        std::cout << "Total allocations: " << total_allocations << std::endl;
        std::cout << "Total deallocations: " << total_deallocations << std::endl;
        std::cout << "Currently allocated: " << (total_allocations - total_deallocations) << " objects" << std::endl;
        std::cout << "Current memory usage: " << format_bytes(current_memory_usage) << std::endl;
        std::cout << "Peak memory usage: " << format_bytes(peak_memory_usage) << std::endl;

        if (total_allocations > 0) {
            size_t avg_size = peak_memory_usage / total_allocations;
            std::cout << "Average allocation size: " << format_bytes(avg_size) << std::endl;
        }
    }

    void print_size_distribution() const {
        std::cout << "\n=== Allocation Size Distribution ===" << std::endl;
        std::cout << std::setw(12) << "Size" << std::setw(12) << "Count"
                  << std::setw(16) << "Total Memory" << std::setw(12) << "% of Total" << std::endl;
        std::cout << std::string(52, '-') << std::endl;

        // Sort by total memory usage (descending)
        std::vector<std::pair<size_t, AllocationStats>> sorted_stats;
        for (const auto& [size, stats] : size_stats) {
            sorted_stats.emplace_back(size, stats);
        }
        std::sort(sorted_stats.begin(), sorted_stats.end(),
                  [](const auto& a, const auto& b) { return a.second.total_size > b.second.total_size; });

        // Show top 20 allocation sizes
        size_t shown = 0;
        size_t total_memory = peak_memory_usage;

        for (const auto& [size, stats] : sorted_stats) {
            if (shown++ >= 20) break;

            double percentage = (total_memory > 0) ? (100.0 * stats.total_size / total_memory) : 0.0;

            std::cout << std::setw(12) << format_bytes(size)
                      << std::setw(12) << stats.total_count
                      << std::setw(16) << format_bytes(stats.total_size)
                      << std::setw(11) << std::fixed << std::setprecision(2) << percentage << "%"
                      << std::endl;
        }
    }

    void print_location_statistics() const {
        if (location_stats.empty()) return;

        std::cout << "\n=== Allocation Location Statistics ===" << std::endl;
        std::cout << std::setw(30) << "Location" << std::setw(12) << "Count"
                  << std::setw(16) << "Total Memory" << std::setw(12) << "% of Total" << std::endl;
        std::cout << std::string(70, '-') << std::endl;

        // Sort by total memory usage (descending)
        std::vector<std::pair<std::string, AllocationStats>> sorted_locations;
        for (const auto& [location, stats] : location_stats) {
            sorted_locations.emplace_back(location, stats);
        }
        std::sort(sorted_locations.begin(), sorted_locations.end(),
                  [](const auto& a, const auto& b) { return a.second.total_size > b.second.total_size; });

        // Show top 15 locations
        size_t shown = 0;
        size_t total_memory = peak_memory_usage;

        for (const auto& [location, stats] : sorted_locations) {
            if (shown++ >= 15) break;

            double percentage = (total_memory > 0) ? (100.0 * stats.total_size / total_memory) : 0.0;

            std::string display_location = location;
            if (display_location.length() > 28) {
                display_location = "..." + display_location.substr(display_location.length() - 25);
            }

            std::cout << std::setw(30) << display_location
                      << std::setw(12) << stats.total_count
                      << std::setw(16) << format_bytes(stats.total_size)
                      << std::setw(11) << std::fixed << std::setprecision(2) << percentage << "%"
                      << std::endl;
        }
    }

    void export_csv(const std::string& filename) const {
        std::ofstream file(filename);
        file << "allocation_size,count,total_memory,percentage" << std::endl;

        size_t total_memory = peak_memory_usage;
        for (const auto& [size, stats] : size_stats) {
            double percentage = (total_memory > 0) ? (100.0 * stats.total_size / total_memory) : 0.0;
            file << size << "," << stats.total_count << "," << stats.total_size << "," << percentage << std::endl;
        }

        std::cout << "Allocation data exported to " << filename << std::endl;
    }

    void enable() { enabled = true; }
    void disable() { enabled = false; }

    size_t get_current_usage() const { return current_memory_usage; }
    size_t get_peak_usage() const { return peak_memory_usage; }
    size_t get_total_allocations() const { return total_allocations; }

private:
    static std::string format_bytes(size_t bytes) {
        const char* suffixes[] = {"B", "KB", "MB", "GB"};
        int suffix_index = 0;
        double size = static_cast<double>(bytes);

        while (size >= 1024.0 && suffix_index < 3) {
            size /= 1024.0;
            suffix_index++;
        }

        std::ostringstream oss;
        oss << std::fixed << std::setprecision(1) << size << suffixes[suffix_index];
        return oss.str();
    }
};

/**
 * Mock Z3-style allocator profiling
 * This simulates various allocation patterns found in Z3
 */
class Z3AllocationSimulator {
private:
    AllocationProfiler& profiler;
    std::vector<void*> allocated_objects;

public:
    explicit Z3AllocationSimulator(AllocationProfiler& prof) : profiler(prof) {}

    ~Z3AllocationSimulator() {
        cleanup_all();
    }

    void simulate_ast_allocations(int count) {
        std::cout << "Simulating " << count << " AST node allocations..." << std::endl;

        // Simulate typical AST node sizes based on Z3's implementation
        std::vector<size_t> ast_sizes = {
            32,   // Small AST nodes (variables, constants)
            48,   // Medium AST nodes (binary operations)
            64,   // Application nodes
            96,   // Function declarations
            128,  // Complex expressions
            256,  // Large compound expressions
            512   // Very large expressions
        };

        for (int i = 0; i < count; i++) {
            size_t size = ast_sizes[i % ast_sizes.size()];
            void* ptr = malloc(size);
            if (ptr) {
                profiler.record_allocation(ptr, size, "AST_node");
                allocated_objects.push_back(ptr);
            }

            // Occasionally allocate larger objects (quantifiers, complex terms)
            if (i % 50 == 0) {
                size_t large_size = 1024 + (i % 2048);
                void* large_ptr = malloc(large_size);
                if (large_ptr) {
                    profiler.record_allocation(large_ptr, large_size, "Complex_AST");
                    allocated_objects.push_back(large_ptr);
                }
            }
        }
    }

    void simulate_hash_table_allocations(int table_count) {
        std::cout << "Simulating " << table_count << " hash table allocations..." << std::endl;

        for (int i = 0; i < table_count; i++) {
            // Simulate initial hash table bucket array
            size_t bucket_size = 16 * sizeof(void*); // 16 initial buckets
            void* buckets = malloc(bucket_size);
            if (buckets) {
                profiler.record_allocation(buckets, bucket_size, "Hash_table_buckets");
                allocated_objects.push_back(buckets);
            }

            // Simulate hash table entries
            int entry_count = 10 + (i % 100);
            for (int j = 0; j < entry_count; j++) {
                size_t entry_size = 24; // Typical hash entry size
                void* entry = malloc(entry_size);
                if (entry) {
                    profiler.record_allocation(entry, entry_size, "Hash_entry");
                    allocated_objects.push_back(entry);
                }
            }

            // Simulate hash table expansion
            if (i % 10 == 0) {
                size_t expanded_size = bucket_size * 2;
                void* expanded = malloc(expanded_size);
                if (expanded) {
                    profiler.record_allocation(expanded, expanded_size, "Hash_table_expansion");
                    allocated_objects.push_back(expanded);
                }
            }
        }
    }

    void simulate_clause_allocations(int clause_count) {
        std::cout << "Simulating " << clause_count << " SAT clause allocations..." << std::endl;

        for (int i = 0; i < clause_count; i++) {
            // Simulate clauses of varying lengths
            int clause_length = 2 + (i % 10); // 2-11 literals per clause
            size_t clause_size = 16 + (clause_length * sizeof(int)); // Header + literals

            void* clause = malloc(clause_size);
            if (clause) {
                profiler.record_allocation(clause, clause_size, "SAT_clause");
                allocated_objects.push_back(clause);
            }

            // Simulate watch lists
            if (i % 3 == 0) {
                size_t watch_size = 8 * sizeof(void*); // Watch list entries
                void* watch_list = malloc(watch_size);
                if (watch_list) {
                    profiler.record_allocation(watch_list, watch_size, "Watch_list");
                    allocated_objects.push_back(watch_list);
                }
            }
        }
    }

    void simulate_string_allocations(int string_count) {
        std::cout << "Simulating " << string_count << " string/symbol allocations..." << std::endl;

        // Simulate symbol table strings of various lengths
        std::vector<size_t> string_lengths = {4, 8, 16, 32, 64, 128, 256};

        for (int i = 0; i < string_count; i++) {
            size_t len = string_lengths[i % string_lengths.size()];
            void* str = malloc(len + 1); // +1 for null terminator
            if (str) {
                profiler.record_allocation(str, len + 1, "Symbol_string");
                allocated_objects.push_back(str);
            }
        }
    }

    void simulate_theory_solver_allocations(int count) {
        std::cout << "Simulating " << count << " theory solver allocations..." << std::endl;

        for (int i = 0; i < count; i++) {
            // Simulate linear arithmetic matrix entries
            size_t matrix_entry_size = 24; // Coefficient, variable, constraint info
            void* entry = malloc(matrix_entry_size);
            if (entry) {
                profiler.record_allocation(entry, matrix_entry_size, "LA_matrix_entry");
                allocated_objects.push_back(entry);
            }

            // Simulate array theory elements
            if (i % 5 == 0) {
                size_t array_elem_size = 32;
                void* elem = malloc(array_elem_size);
                if (elem) {
                    profiler.record_allocation(elem, array_elem_size, "Array_element");
                    allocated_objects.push_back(elem);
                }
            }

            // Simulate bit-vector theory elements
            if (i % 7 == 0) {
                size_t bv_size = 16 + (i % 64); // Variable bit-width
                void* bv = malloc(bv_size);
                if (bv) {
                    profiler.record_allocation(bv, bv_size, "Bitvector");
                    allocated_objects.push_back(bv);
                }
            }
        }
    }

    void cleanup_all() {
        std::cout << "Cleaning up allocated objects..." << std::endl;
        for (void* ptr : allocated_objects) {
            profiler.record_deallocation(ptr);
            free(ptr);
        }
        allocated_objects.clear();
    }

    void partial_cleanup(double fraction) {
        size_t to_remove = static_cast<size_t>(allocated_objects.size() * fraction);
        std::cout << "Performing partial cleanup of " << to_remove << " objects..." << std::endl;

        for (size_t i = 0; i < to_remove && !allocated_objects.empty(); i++) {
            void* ptr = allocated_objects.back();
            allocated_objects.pop_back();
            profiler.record_deallocation(ptr);
            free(ptr);
        }
    }
};

/**
 * Main benchmark function
 */
void run_allocation_benchmark() {
    AllocationProfiler profiler;
    Z3AllocationSimulator simulator(profiler);

    std::cout << "=== Z3 Memory Allocation Pattern Profiler ===" << std::endl;
    std::cout << "This tool simulates Z3's allocation patterns to identify bottlenecks." << std::endl;
    std::cout << std::endl;

    auto start_time = std::chrono::high_resolution_clock::now();

    // Simulate different allocation patterns that occur in Z3
    simulator.simulate_ast_allocations(5000);
    simulator.simulate_hash_table_allocations(100);
    simulator.simulate_clause_allocations(2000);
    simulator.simulate_string_allocations(1000);
    simulator.simulate_theory_solver_allocations(3000);

    // Simulate some garbage collection / deallocation
    simulator.partial_cleanup(0.3); // Clean up 30% of objects

    // Continue with more allocations
    simulator.simulate_ast_allocations(2000);
    simulator.simulate_hash_table_allocations(50);

    auto end_time = std::chrono::high_resolution_clock::now();
    auto duration = std::chrono::duration_cast<std::chrono::milliseconds>(end_time - start_time);

    profiler.print_summary();
    profiler.print_size_distribution();
    profiler.print_location_statistics();
    profiler.export_csv("z3_allocation_profile.csv");

    std::cout << "\nBenchmark completed in " << duration.count() << " ms" << std::endl;

    std::cout << "\n=== Key Insights ===" << std::endl;
    std::cout << "1. Monitor allocation sizes that dominate memory usage" << std::endl;
    std::cout << "2. Look for fragmentation patterns in size distribution" << std::endl;
    std::cout << "3. Identify components with heaviest allocation patterns" << std::endl;
    std::cout << "4. Consider memory pool optimization for common sizes" << std::endl;
    std::cout << "5. Profile real Z3 workloads to validate these patterns" << std::endl;
}

int main(int argc, char* argv[]) {
    bool help = false;

    for (int i = 1; i < argc; i++) {
        if (std::string(argv[i]) == "--help") {
            help = true;
            break;
        }
    }

    if (help) {
        std::cout << "Z3 Memory Allocation Profiler" << std::endl;
        std::cout << "Usage: " << argv[0] << " [--help]" << std::endl;
        std::cout << std::endl;
        std::cout << "This tool simulates Z3's memory allocation patterns to help identify" << std::endl;
        std::cout << "memory bottlenecks and optimization opportunities." << std::endl;
        std::cout << std::endl;
        std::cout << "Output files:" << std::endl;
        std::cout << "  z3_allocation_profile.csv - Detailed allocation statistics" << std::endl;
        return 0;
    }

    run_allocation_benchmark();
    return 0;
}