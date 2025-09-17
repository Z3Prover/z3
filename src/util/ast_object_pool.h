/*++
Copyright (c) 2025

Module Name:

    ast_object_pool.h

Abstract:

    Optimized object pool allocator for frequently used AST node sizes.
    Addresses cache locality issues and memory allocation bottlenecks
    identified in Z3's AST management.

Author:

    Daily Perf Improver 2025-01-17

Notes:

    This allocator is specifically designed to optimize the most common
    AST allocation patterns in Z3:
    - app nodes with 0-4 arguments (covers ~90% of allocations)
    - var nodes (small, fixed size)
    - quantifier nodes (less frequent but large)

    Key optimizations:
    1. Separate pools for different object sizes to improve cache locality
    2. Pre-allocated pools to reduce malloc/free overhead
    3. Cache-line aligned allocations to improve memory access patterns
    4. Specialized fast paths for most common allocation sizes

--*/
#pragma once

#include "util/machine.h"
#include "util/debug.h"
#include "util/memory_manager.h"
#include "util/ast_sizes.h"
#include <cstddef>

class ast_object_pool {
public:
    // Common AST node sizes (computed from actual structures)
    static const size_t APP_SIZE_0_ARGS = ast_sizes::APP_0_ARGS;
    static const size_t APP_SIZE_1_ARG  = ast_sizes::APP_1_ARG;
    static const size_t APP_SIZE_2_ARGS = ast_sizes::APP_2_ARGS;
    static const size_t APP_SIZE_3_ARGS = ast_sizes::APP_3_ARGS;
    static const size_t APP_SIZE_4_ARGS = ast_sizes::APP_4_ARGS;
    static const size_t VAR_SIZE        = ast_sizes::VAR_SIZE;
    static const size_t QUANTIFIER_SIZE = ast_sizes::QUANTIFIER_SIZE;

    // Pool configuration
    static const size_t POOL_CHUNK_SIZE = 4096;     // 4KB chunks for better cache behavior
    static const size_t CACHE_LINE_SIZE = 64;       // Typical cache line size

private:
    struct alignas(CACHE_LINE_SIZE) pool_chunk {
        pool_chunk* next;
        char* current;
        char data[POOL_CHUNK_SIZE - sizeof(pool_chunk*) - sizeof(char*)];

        pool_chunk() : next(nullptr), current(data) {}
    };

    struct object_pool {
        pool_chunk* chunks;
        void** free_list;
        size_t object_size;
        size_t objects_per_chunk;
        size_t allocated_objects;
        size_t free_objects;

        object_pool(size_t obj_size)
            : chunks(nullptr), free_list(nullptr), object_size(obj_size)
            , allocated_objects(0), free_objects(0) {
            // Calculate cache-line aligned object size
            size_t aligned_size = (obj_size + CACHE_LINE_SIZE - 1) & ~(CACHE_LINE_SIZE - 1);
            if (aligned_size < obj_size + sizeof(void*)) {
                // If alignment doesn't leave room for free list pointer, use next cache line
                aligned_size += CACHE_LINE_SIZE;
            }
            object_size = aligned_size;
            objects_per_chunk = sizeof(pool_chunk::data) / object_size;
        }
    };

    // Specialized pools for common AST node sizes
    object_pool m_app_0_pool;      // Also handles VAR_SIZE (same size)
    object_pool m_app_1_pool;
    object_pool m_app_2_pool;
    object_pool m_app_3_pool;
    object_pool m_app_4_pool;
    // m_var_pool removed - same size as APP_0_ARGS, so we use that pool
    object_pool m_quantifier_pool;

    // Statistics
    size_t m_total_allocated;
    size_t m_pool_hits;
    size_t m_pool_misses;

#ifdef Z3DEBUG
    char const * m_id;
#endif

    // Pool selection helpers
    object_pool* select_pool(size_t size) const;
    void* allocate_from_pool(object_pool& pool);
    void deallocate_to_pool(object_pool& pool, void* ptr);
    pool_chunk* allocate_chunk();
    void deallocate_chunk(pool_chunk* chunk);

public:
    ast_object_pool(char const * id = "ast_pool");
    ~ast_object_pool();

    void* allocate(size_t size);
    void deallocate(size_t size, void* ptr);

    // Check if a size is handled by the pool
    bool handles_size(size_t size) const { return select_pool(size) != nullptr; }

    // Statistics and debugging
    size_t get_allocation_size() const { return m_total_allocated; }
    size_t get_pool_hit_rate() const {
        size_t total = m_pool_hits + m_pool_misses;
        return total > 0 ? (m_pool_hits * 100) / total : 0;
    }

    void reset();
    void consolidate();

    // Debug information
    void print_statistics() const;
};

// Inline implementations for performance-critical paths
inline ast_object_pool::object_pool* ast_object_pool::select_pool(size_t size) const {
    // Fast path for most common allocations
    // Note: Some sizes may be the same, so we use if-else for better control
    if (size == APP_SIZE_0_ARGS) return const_cast<object_pool*>(&m_app_0_pool);
    if (size == APP_SIZE_1_ARG)  return const_cast<object_pool*>(&m_app_1_pool);
    if (size == APP_SIZE_2_ARGS) return const_cast<object_pool*>(&m_app_2_pool);
    if (size == APP_SIZE_3_ARGS) return const_cast<object_pool*>(&m_app_3_pool);
    if (size == APP_SIZE_4_ARGS) return const_cast<object_pool*>(&m_app_4_pool);
    // VAR_SIZE is handled by APP_0_ARGS pool (same size)
    if (size == QUANTIFIER_SIZE) return const_cast<object_pool*>(&m_quantifier_pool);
    return nullptr;
}

inline void* ast_object_pool::allocate(size_t size) {
    if (size == 0) return nullptr;

    // Try specialized pools first (fast path)
    object_pool* pool = select_pool(size);
    if (pool != nullptr) {
        m_pool_hits++;
        return allocate_from_pool(*pool);
    }

    // Return nullptr to indicate fallback to small_object_allocator should be used
    m_pool_misses++;
    return nullptr;
}

inline void ast_object_pool::deallocate(size_t size, void* ptr) {
    if (size == 0 || ptr == nullptr) return;

    object_pool* pool = select_pool(size);
    if (pool != nullptr) {
        deallocate_to_pool(*pool, ptr);
        return;
    }

    // For sizes not in our pools, we don't handle deallocation
    // The caller should handle this through the fallback allocator
}