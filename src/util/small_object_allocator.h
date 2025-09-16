/*++
Copyright (c) 2006 Microsoft Corporation

Module Name:

    small_object_allocator.h

Abstract:

    Small object allocator.

Author:

    Nikolaj bjorner (nbjorner) 2007-08-06.

Revision History:
    Leonardo de Moura (leonardo) 2011-04-27
    Rewrote/Simplified the allocator
--*/
#pragma once

#include "util/machine.h"
#include "util/debug.h"
#include "util/trace.h"

class small_object_allocator {
    static const unsigned CHUNK_SIZE     = (8192 - sizeof(void*)*2);
    static const unsigned SMALL_OBJ_SIZE = 256;
    static const unsigned NUM_SLOTS      = (SMALL_OBJ_SIZE >> PTR_ALIGNMENT);

    // Common size pools for better cache locality
    static const unsigned NUM_COMMON_POOLS = 4;
    static const unsigned COMMON_SIZES[NUM_COMMON_POOLS];
    static const unsigned POOL_CHUNK_SIZE = 4096;

    struct chunk {
        chunk* m_next{ nullptr };
        char* m_curr = m_data;
        char    m_data[CHUNK_SIZE];

        // Cache-aligned chunk allocation
        void prefetch_next() const {
#ifdef __builtin_prefetch
            if (m_next) __builtin_prefetch(m_next, 0, 3);
#endif
        }
    };

    // Pool-based allocation for common sizes
    struct pool_chunk {
        pool_chunk* m_next{ nullptr };
        unsigned m_obj_size;
        unsigned m_objects_per_chunk;
        unsigned m_free_count;
        void* m_free_head;
        char m_data[POOL_CHUNK_SIZE];

        pool_chunk(unsigned obj_size) : m_obj_size(obj_size) {
            m_objects_per_chunk = POOL_CHUNK_SIZE / obj_size;
            m_free_count = m_objects_per_chunk;
            // Initialize free list in pool
            init_free_list();
        }

        void init_free_list();
        void* allocate();
        void deallocate(void* p);
        bool is_empty() const { return m_free_count == m_objects_per_chunk; }
        bool contains(void* p) const {
            return p >= m_data && p < m_data + POOL_CHUNK_SIZE;
        }
    };

    chunk *     m_chunks[NUM_SLOTS];
    void  *     m_free_list[NUM_SLOTS];
    pool_chunk* m_pools[NUM_COMMON_POOLS];
    size_t      m_alloc_size;
    size_t      m_pool_hits;
    size_t      m_total_allocs;
#ifdef Z3DEBUG
    char const * m_id;
#endif

    unsigned get_pool_index(size_t size) const;
    pool_chunk* get_or_create_pool(unsigned pool_idx);
public:
    small_object_allocator(char const * id = "unknown");
    ~small_object_allocator();
    void reset();
    void * allocate(size_t size);
    void deallocate(size_t size, void * p);
    size_t get_allocation_size() const { return m_alloc_size; }
    size_t get_wasted_size() const;
    size_t get_num_free_objs() const;
    void consolidate();

    // Performance monitoring
    double get_pool_hit_ratio() const {
        return m_total_allocs > 0 ? (double)m_pool_hits / m_total_allocs : 0.0;
    }
    size_t get_pool_hits() const { return m_pool_hits; }
    size_t get_total_allocs() const { return m_total_allocs; }
};

inline void * operator new(size_t s, small_object_allocator & r) { return r.allocate(s); }
inline void * operator new[](size_t s, small_object_allocator & r) { return r.allocate(s); }
inline void operator delete(void * p, small_object_allocator & r) { UNREACHABLE(); }
inline void operator delete[](void * p, small_object_allocator & r) { UNREACHABLE(); }


