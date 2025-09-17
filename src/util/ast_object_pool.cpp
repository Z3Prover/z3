/*++
Copyright (c) 2025

Module Name:

    ast_object_pool.cpp

Abstract:

    Implementation of optimized object pool allocator for AST nodes.

--*/
#include "util/ast_object_pool.h"
#include "util/debug.h"
#include <iostream>
#include <iomanip>

ast_object_pool::ast_object_pool(char const * id)
    : m_app_0_pool(APP_SIZE_0_ARGS)
    , m_app_1_pool(APP_SIZE_1_ARG)
    , m_app_2_pool(APP_SIZE_2_ARGS)
    , m_app_3_pool(APP_SIZE_3_ARGS)
    , m_app_4_pool(APP_SIZE_4_ARGS)
    , m_quantifier_pool(QUANTIFIER_SIZE)
    , m_total_allocated(0)
    , m_pool_hits(0)
    , m_pool_misses(0) {
    DEBUG_CODE({
        m_id = id;
    });
}

ast_object_pool::~ast_object_pool() {
    reset();
    DEBUG_CODE({
        if (m_total_allocated > 0) {
            std::cerr << "Memory leak detected in ast_object_pool '" << m_id
                     << "'. " << m_total_allocated << " bytes leaked" << std::endl;
        }
    });
}

void ast_object_pool::reset() {
    // Reset all pools
    object_pool* pools[] = {
        &m_app_0_pool, &m_app_1_pool, &m_app_2_pool,
        &m_app_3_pool, &m_app_4_pool, &m_quantifier_pool
    };

    for (auto pool : pools) {
        pool_chunk* chunk = pool->chunks;
        while (chunk != nullptr) {
            pool_chunk* next = chunk->next;
            deallocate_chunk(chunk);
            chunk = next;
        }
        pool->chunks = nullptr;
        pool->free_list = nullptr;
        pool->allocated_objects = 0;
        pool->free_objects = 0;
    }

    m_total_allocated = 0;
    m_pool_hits = 0;
    m_pool_misses = 0;
}

ast_object_pool::pool_chunk* ast_object_pool::allocate_chunk() {
    void* mem = memory::allocate(sizeof(pool_chunk));
    return new (mem) pool_chunk();
}

void ast_object_pool::deallocate_chunk(pool_chunk* chunk) {
    chunk->~pool_chunk();
    memory::deallocate(chunk);
}

void* ast_object_pool::allocate_from_pool(object_pool& pool) {
    // Fast path: use free list if available
    if (pool.free_list != nullptr) {
        void** result = pool.free_list;
        pool.free_list = reinterpret_cast<void**>(*pool.free_list);
        pool.free_objects--;
        pool.allocated_objects++;
        return result;
    }

    // Slow path: allocate from current chunk or create new chunk
    pool_chunk* chunk = pool.chunks;
    if (chunk == nullptr ||
        chunk->current + pool.object_size > chunk->data + sizeof(chunk->data)) {

        // Need a new chunk
        pool_chunk* new_chunk = allocate_chunk();
        new_chunk->next = pool.chunks;
        pool.chunks = new_chunk;
        chunk = new_chunk;
        m_total_allocated += sizeof(pool_chunk);
    }

    void* result = chunk->current;
    chunk->current += pool.object_size;
    pool.allocated_objects++;

    return result;
}

void ast_object_pool::deallocate_to_pool(object_pool& pool, void* ptr) {
    SASSERT(ptr != nullptr);

    // Add to free list for fast reallocation
    *reinterpret_cast<void**>(ptr) = pool.free_list;
    pool.free_list = reinterpret_cast<void**>(ptr);
    pool.free_objects++;
    pool.allocated_objects--;
}

void ast_object_pool::consolidate() {
    // Consolidation strategy: if a pool has many free objects relative to
    // allocated objects, we could consider compacting or returning memory.
    // For now, we'll just report statistics.

    DEBUG_CODE({
        std::cerr << "ast_object_pool consolidation statistics for '" << m_id << "':" << std::endl;
        print_statistics();
    });
}

void ast_object_pool::print_statistics() const {
    struct pool_info {
        const char* name;
        const object_pool* pool;
    };

    pool_info pools[] = {
        {"app_0/var", &m_app_0_pool},
        {"app_1", &m_app_1_pool},
        {"app_2", &m_app_2_pool},
        {"app_3", &m_app_3_pool},
        {"app_4", &m_app_4_pool},
        {"quantifier", &m_quantifier_pool}
    };

    std::cerr << std::setw(12) << "Pool"
              << std::setw(10) << "ObjSize"
              << std::setw(12) << "Allocated"
              << std::setw(10) << "Free"
              << std::setw(12) << "Efficiency" << std::endl;

    for (const auto& info : pools) {
        size_t total_objs = info.pool->allocated_objects + info.pool->free_objects;
        double efficiency = total_objs > 0 ?
            (double)info.pool->allocated_objects / total_objs * 100.0 : 0.0;

        std::cerr << std::setw(12) << info.name
                  << std::setw(10) << info.pool->object_size
                  << std::setw(12) << info.pool->allocated_objects
                  << std::setw(10) << info.pool->free_objects
                  << std::setw(11) << std::fixed << std::setprecision(1) << efficiency << "%"
                  << std::endl;
    }

    std::cerr << "\nTotal allocated: " << m_total_allocated << " bytes" << std::endl;
    std::cerr << "Pool hit rate: " << get_pool_hit_rate() << "%" << std::endl;
}