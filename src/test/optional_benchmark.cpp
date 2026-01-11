/*++
Copyright (c) 2006 Microsoft Corporation

Module Name:

    optional_benchmark.cpp

Abstract:

    Benchmark std::optional vs custom optional implementation

Author:

    GitHub Copilot 2026-01-11

Revision History:

--*/

#include "util/trace.h"
#include "util/debug.h"
#include "util/memory_manager.h"
#include "util/optional.h"
#include <optional>
#include <chrono>
#include <iostream>
#include <iomanip>

// Simple struct for testing
struct BenchData {
    int x;
    int y;
    int z;
    
    BenchData(int a = 0, int b = 0, int c = 0) : x(a), y(b), z(c) {}
};

// Benchmark helper
template<typename Func>
double measure_time_ms(Func f, int iterations = 1000000) {
    auto start = std::chrono::high_resolution_clock::now();
    f();
    auto end = std::chrono::high_resolution_clock::now();
    std::chrono::duration<double, std::milli> elapsed = end - start;
    return elapsed.count();
}

// Prevent compiler optimization
template<typename T>
void do_not_optimize(T const& value) {
    asm volatile("" : "+m"(const_cast<T&>(value)));
}

void benchmark_construction() {
    const int iterations = 1000000;
    
    std::cout << "\n=== Construction Benchmark ===" << std::endl;
    
    // Test 1: Default construction
    {
        double custom_time = measure_time_ms([&]() {
            for (int i = 0; i < iterations; i++) {
                optional<int> opt;
                do_not_optimize(opt);
            }
        });
        
        double std_time = measure_time_ms([&]() {
            for (int i = 0; i < iterations; i++) {
                std::optional<int> opt;
                do_not_optimize(opt);
            }
        });
        
        std::cout << "Default construction (int):" << std::endl;
        std::cout << "  Custom optional: " << std::fixed << std::setprecision(2) 
                  << custom_time << " ms" << std::endl;
        std::cout << "  std::optional:   " << std::fixed << std::setprecision(2) 
                  << std_time << " ms" << std::endl;
        std::cout << "  Ratio (custom/std): " << std::fixed << std::setprecision(2) 
                  << (custom_time / std_time) << "x" << std::endl;
    }
    
    // Test 2: Value construction
    {
        double custom_time = measure_time_ms([&]() {
            for (int i = 0; i < iterations; i++) {
                optional<int> opt(i);
                do_not_optimize(opt);
            }
        });
        
        double std_time = measure_time_ms([&]() {
            for (int i = 0; i < iterations; i++) {
                std::optional<int> opt(i);
                do_not_optimize(opt);
            }
        });
        
        std::cout << "\nValue construction (int):" << std::endl;
        std::cout << "  Custom optional: " << std::fixed << std::setprecision(2) 
                  << custom_time << " ms" << std::endl;
        std::cout << "  std::optional:   " << std::fixed << std::setprecision(2) 
                  << std_time << " ms" << std::endl;
        std::cout << "  Ratio (custom/std): " << std::fixed << std::setprecision(2) 
                  << (custom_time / std_time) << "x" << std::endl;
    }
    
    // Test 3: Struct construction
    {
        double custom_time = measure_time_ms([&]() {
            for (int i = 0; i < iterations; i++) {
                optional<BenchData> opt(BenchData(i, i+1, i+2));
                do_not_optimize(opt);
            }
        });
        
        double std_time = measure_time_ms([&]() {
            for (int i = 0; i < iterations; i++) {
                std::optional<BenchData> opt(BenchData(i, i+1, i+2));
                do_not_optimize(opt);
            }
        });
        
        std::cout << "\nValue construction (struct):" << std::endl;
        std::cout << "  Custom optional: " << std::fixed << std::setprecision(2) 
                  << custom_time << " ms" << std::endl;
        std::cout << "  std::optional:   " << std::fixed << std::setprecision(2) 
                  << std_time << " ms" << std::endl;
        std::cout << "  Ratio (custom/std): " << std::fixed << std::setprecision(2) 
                  << (custom_time / std_time) << "x" << std::endl;
    }
}

void benchmark_copy() {
    const int iterations = 1000000;
    
    std::cout << "\n=== Copy Benchmark ===" << std::endl;
    
    // Test 1: Copy construction (int)
    {
        optional<int> custom_src(42);
        std::optional<int> std_src(42);
        
        double custom_time = measure_time_ms([&]() {
            for (int i = 0; i < iterations; i++) {
                optional<int> opt(custom_src);
                do_not_optimize(opt);
            }
        });
        
        double std_time = measure_time_ms([&]() {
            for (int i = 0; i < iterations; i++) {
                std::optional<int> opt(std_src);
                do_not_optimize(opt);
            }
        });
        
        std::cout << "Copy construction (int):" << std::endl;
        std::cout << "  Custom optional: " << std::fixed << std::setprecision(2) 
                  << custom_time << " ms" << std::endl;
        std::cout << "  std::optional:   " << std::fixed << std::setprecision(2) 
                  << std_time << " ms" << std::endl;
        std::cout << "  Ratio (custom/std): " << std::fixed << std::setprecision(2) 
                  << (custom_time / std_time) << "x" << std::endl;
    }
    
    // Test 2: Copy assignment (int)
    {
        optional<int> custom_src(42);
        std::optional<int> std_src(42);
        
        double custom_time = measure_time_ms([&]() {
            for (int i = 0; i < iterations; i++) {
                optional<int> opt;
                opt = custom_src;
                do_not_optimize(opt);
            }
        });
        
        double std_time = measure_time_ms([&]() {
            for (int i = 0; i < iterations; i++) {
                std::optional<int> opt;
                opt = std_src;
                do_not_optimize(opt);
            }
        });
        
        std::cout << "\nCopy assignment (int):" << std::endl;
        std::cout << "  Custom optional: " << std::fixed << std::setprecision(2) 
                  << custom_time << " ms" << std::endl;
        std::cout << "  std::optional:   " << std::fixed << std::setprecision(2) 
                  << std_time << " ms" << std::endl;
        std::cout << "  Ratio (custom/std): " << std::fixed << std::setprecision(2) 
                  << (custom_time / std_time) << "x" << std::endl;
    }
}

void benchmark_move() {
    const int iterations = 1000000;
    
    std::cout << "\n=== Move Benchmark ===" << std::endl;
    
    // Test 1: Move construction (int)
    {
        double custom_time = measure_time_ms([&]() {
            for (int i = 0; i < iterations; i++) {
                optional<int> src(i);
                optional<int> dst(std::move(src));
                do_not_optimize(dst);
            }
        });
        
        double std_time = measure_time_ms([&]() {
            for (int i = 0; i < iterations; i++) {
                std::optional<int> src(i);
                std::optional<int> dst(std::move(src));
                do_not_optimize(dst);
            }
        });
        
        std::cout << "Move construction (int):" << std::endl;
        std::cout << "  Custom optional: " << std::fixed << std::setprecision(2) 
                  << custom_time << " ms" << std::endl;
        std::cout << "  std::optional:   " << std::fixed << std::setprecision(2) 
                  << std_time << " ms" << std::endl;
        std::cout << "  Ratio (custom/std): " << std::fixed << std::setprecision(2) 
                  << (custom_time / std_time) << "x" << std::endl;
    }
    
    // Test 2: Move assignment (int)
    {
        double custom_time = measure_time_ms([&]() {
            for (int i = 0; i < iterations; i++) {
                optional<int> src(i);
                optional<int> dst;
                dst = std::move(src);
                do_not_optimize(dst);
            }
        });
        
        double std_time = measure_time_ms([&]() {
            for (int i = 0; i < iterations; i++) {
                std::optional<int> src(i);
                std::optional<int> dst;
                dst = std::move(src);
                do_not_optimize(dst);
            }
        });
        
        std::cout << "\nMove assignment (int):" << std::endl;
        std::cout << "  Custom optional: " << std::fixed << std::setprecision(2) 
                  << custom_time << " ms" << std::endl;
        std::cout << "  std::optional:   " << std::fixed << std::setprecision(2) 
                  << std_time << " ms" << std::endl;
        std::cout << "  Ratio (custom/std): " << std::fixed << std::setprecision(2) 
                  << (custom_time / std_time) << "x" << std::endl;
    }
}

void benchmark_access() {
    const int iterations = 10000000;
    
    std::cout << "\n=== Access Benchmark ===" << std::endl;
    
    // Test 1: Dereference operator
    {
        optional<int> custom_opt(42);
        std::optional<int> std_opt(42);
        
        double custom_time = measure_time_ms([&]() {
            int sum = 0;
            for (int i = 0; i < iterations; i++) {
                sum += *custom_opt;
            }
            do_not_optimize(sum);
        });
        
        double std_time = measure_time_ms([&]() {
            int sum = 0;
            for (int i = 0; i < iterations; i++) {
                sum += *std_opt;
            }
            do_not_optimize(sum);
        });
        
        std::cout << "Dereference operator (int):" << std::endl;
        std::cout << "  Custom optional: " << std::fixed << std::setprecision(2) 
                  << custom_time << " ms" << std::endl;
        std::cout << "  std::optional:   " << std::fixed << std::setprecision(2) 
                  << std_time << " ms" << std::endl;
        std::cout << "  Ratio (custom/std): " << std::fixed << std::setprecision(2) 
                  << (custom_time / std_time) << "x" << std::endl;
    }
    
    // Test 2: Arrow operator
    {
        optional<BenchData> custom_opt(BenchData(1, 2, 3));
        std::optional<BenchData> std_opt(BenchData(1, 2, 3));
        
        double custom_time = measure_time_ms([&]() {
            int sum = 0;
            for (int i = 0; i < iterations; i++) {
                sum += custom_opt->x;
            }
            do_not_optimize(sum);
        });
        
        double std_time = measure_time_ms([&]() {
            int sum = 0;
            for (int i = 0; i < iterations; i++) {
                sum += std_opt->x;
            }
            do_not_optimize(sum);
        });
        
        std::cout << "\nArrow operator (struct):" << std::endl;
        std::cout << "  Custom optional: " << std::fixed << std::setprecision(2) 
                  << custom_time << " ms" << std::endl;
        std::cout << "  std::optional:   " << std::fixed << std::setprecision(2) 
                  << std_time << " ms" << std::endl;
        std::cout << "  Ratio (custom/std): " << std::fixed << std::setprecision(2) 
                  << (custom_time / std_time) << "x" << std::endl;
    }
    
    // Test 3: Boolean conversion
    {
        optional<int> custom_opt(42);
        std::optional<int> std_opt(42);
        
        double custom_time = measure_time_ms([&]() {
            int count = 0;
            for (int i = 0; i < iterations; i++) {
                if (custom_opt) count++;
            }
            do_not_optimize(count);
        });
        
        double std_time = measure_time_ms([&]() {
            int count = 0;
            for (int i = 0; i < iterations; i++) {
                if (std_opt) count++;
            }
            do_not_optimize(count);
        });
        
        std::cout << "\nBoolean conversion:" << std::endl;
        std::cout << "  Custom optional: " << std::fixed << std::setprecision(2) 
                  << custom_time << " ms" << std::endl;
        std::cout << "  std::optional:   " << std::fixed << std::setprecision(2) 
                  << std_time << " ms" << std::endl;
        std::cout << "  Ratio (custom/std): " << std::fixed << std::setprecision(2) 
                  << (custom_time / std_time) << "x" << std::endl;
    }
}

void benchmark_memory() {
    std::cout << "\n=== Memory Footprint ===" << std::endl;
    
    std::cout << "Size of optional<int>:" << std::endl;
    std::cout << "  Custom optional: " << sizeof(optional<int>) << " bytes" << std::endl;
    std::cout << "  std::optional:   " << sizeof(std::optional<int>) << " bytes" << std::endl;
    
    std::cout << "\nSize of optional<BenchData>:" << std::endl;
    std::cout << "  Custom optional: " << sizeof(optional<BenchData>) << " bytes" << std::endl;
    std::cout << "  std::optional:   " << sizeof(std::optional<BenchData>) << " bytes" << std::endl;
    
    std::cout << "\nSize of optional<int*>:" << std::endl;
    std::cout << "  Custom optional: " << sizeof(optional<int*>) << " bytes" << std::endl;
    std::cout << "  std::optional:   " << sizeof(std::optional<int*>) << " bytes" << std::endl;
}

void tst_optional_benchmark() {
    std::cout << "\n╔═══════════════════════════════════════════════════════════════╗" << std::endl;
    std::cout << "║   std::optional vs Custom optional Performance Benchmark     ║" << std::endl;
    std::cout << "╚═══════════════════════════════════════════════════════════════╝" << std::endl;
    
    benchmark_memory();
    benchmark_construction();
    benchmark_copy();
    benchmark_move();
    benchmark_access();
    
    std::cout << "\n═══════════════════════════════════════════════════════════════" << std::endl;
    std::cout << "Benchmark completed!" << std::endl;
    std::cout << "\nNotes:" << std::endl;
    std::cout << "- Custom optional uses heap allocation (alloc/dealloc)" << std::endl;
    std::cout << "- std::optional uses in-place storage (no heap allocation)" << std::endl;
    std::cout << "- Ratios > 1.0 indicate custom optional is slower" << std::endl;
    std::cout << "- Ratios < 1.0 indicate custom optional is faster" << std::endl;
    std::cout << "═══════════════════════════════════════════════════════════════\n" << std::endl;
}
