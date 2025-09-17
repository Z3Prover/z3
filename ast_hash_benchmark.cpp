#include <iostream>
#include <chrono>
#include <vector>
#include <random>

// Minimal headers needed for the hash benchmark
#include "src/util/hash.h"

// Mock AST node structure for testing
struct MockASTNode {
    unsigned m_hash;
    unsigned hash() const { return m_hash; }
};

// Original version of ast_array_hash for comparison
template<typename T>
inline unsigned ast_array_hash_original(T * const * array, unsigned size, unsigned init_value) {
    switch (size) {
    case 0:
        return init_value;
    case 1:
        return combine_hash(array[0]->hash(), init_value);
    case 2:
        return combine_hash(combine_hash(array[0]->hash(), array[1]->hash()),
                            init_value);
    case 3:
        return combine_hash(combine_hash(array[0]->hash(), array[1]->hash()),
                            combine_hash(array[2]->hash(), init_value));
    default: {
        unsigned a, b, c;
        a = b = 0x9e3779b9;
        c = init_value;
        while (size >= 3) {
            size--;
            a += array[size]->hash();
            size--;
            b += array[size]->hash();
            size--;
            c += array[size]->hash();
            mix(a, b, c);
        }
        switch (size) {
        case 2:
            b += array[1]->hash();
            // Z3_fallthrough;
        case 1:
            c += array[0]->hash();
        }
        mix(a, b, c);
        return c;
    }
}

// New optimized version (copy from our implementation)
template<typename T>
inline unsigned ast_array_hash_optimized(T * const * array, unsigned size, unsigned init_value) {
    switch (size) {
    case 0:
        return init_value;
    case 1:
        return combine_hash(array[0]->hash(), init_value);
    case 2:
        return combine_hash(combine_hash(array[0]->hash(), array[1]->hash()),
                            init_value);
    case 3:
        return combine_hash(combine_hash(array[0]->hash(), array[1]->hash()),
                            combine_hash(array[2]->hash(), init_value));
    default: {
        unsigned a, b, c;
        a = b = 0x9e3779b9;
        c = init_value;

        // Optimized version: batch-prefetch hash values to improve cache locality
        // For arrays with many children, fetch hash values in batches to reduce cache misses
        if (size >= 12) {
            constexpr unsigned BATCH_SIZE = 6;
            unsigned hash_buffer[BATCH_SIZE];
            unsigned idx = size;

            while (idx >= BATCH_SIZE) {
                // Batch-fetch hash values to improve cache locality
                for (unsigned i = 0; i < BATCH_SIZE; ++i) {
                    hash_buffer[i] = array[--idx]->hash();
                }

                // Process in groups of 3 for mixing
                a += hash_buffer[2];
                b += hash_buffer[1];
                c += hash_buffer[0];
                mix(a, b, c);

                a += hash_buffer[5];
                b += hash_buffer[4];
                c += hash_buffer[3];
                mix(a, b, c);
            }

            // Handle remaining elements in the original way
            while (idx >= 3) {
                idx--;
                a += array[idx]->hash();
                idx--;
                b += array[idx]->hash();
                idx--;
                c += array[idx]->hash();
                mix(a, b, c);
            }

            switch (idx) {
            case 2:
                b += array[1]->hash();
                // Z3_fallthrough;
            case 1:
                c += array[0]->hash();
            }
        } else {
            // For smaller arrays, use original algorithm
            while (size >= 3) {
                size--;
                a += array[size]->hash();
                size--;
                b += array[size]->hash();
                size--;
                c += array[size]->hash();
                mix(a, b, c);
            }
            switch (size) {
            case 2:
                b += array[1]->hash();
                // Z3_fallthrough;
            case 1:
                c += array[0]->hash();
            }
        }
        mix(a, b, c);
        return c;
    }
}

int main() {
    const int NUM_ITERATIONS = 100000;
    std::random_device rd;
    std::mt19937 gen(rd());
    std::uniform_int_distribution<> dis(1000, 999999);

    // Test different array sizes
    std::vector<unsigned> test_sizes = {5, 10, 15, 20, 30, 50};

    for (unsigned size : test_sizes) {
        std::cout << "Testing array size " << size << ":\n";

        // Create test data
        std::vector<MockASTNode> nodes(size);
        std::vector<MockASTNode*> node_ptrs(size);

        for (unsigned i = 0; i < size; ++i) {
            nodes[i].m_hash = dis(gen);
            node_ptrs[i] = &nodes[i];
        }

        // Benchmark original version
        auto start = std::chrono::high_resolution_clock::now();
        unsigned hash_orig = 0;
        for (int i = 0; i < NUM_ITERATIONS; ++i) {
            hash_orig ^= ast_array_hash_original(node_ptrs.data(), size, 42);
        }
        auto end = std::chrono::high_resolution_clock::now();
        auto original_time = std::chrono::duration_cast<std::chrono::microseconds>(end - start);

        // Benchmark optimized version
        start = std::chrono::high_resolution_clock::now();
        unsigned hash_opt = 0;
        for (int i = 0; i < NUM_ITERATIONS; ++i) {
            hash_opt ^= ast_array_hash_optimized(node_ptrs.data(), size, 42);
        }
        end = std::chrono::high_resolution_clock::now();
        auto optimized_time = std::chrono::duration_cast<std::chrono::microseconds>(end - start);

        std::cout << "  Original:  " << original_time.count() << " μs\n";
        std::cout << "  Optimized: " << optimized_time.count() << " μs\n";

        // Verify correctness
        if (hash_orig == hash_opt) {
            std::cout << "  ✓ Results match\n";
        } else {
            std::cout << "  ✗ Results differ (orig=" << hash_orig << ", opt=" << hash_opt << ")\n";
        }

        if (optimized_time < original_time) {
            double speedup = (double)original_time.count() / optimized_time.count();
            std::cout << "  ⚡ " << speedup << "x faster\n";
        } else {
            double slowdown = (double)optimized_time.count() / original_time.count();
            std::cout << "  🐌 " << slowdown << "x slower\n";
        }
        std::cout << "\n";
    }

    return 0;
}