/*++
Copyright (c) 2007 Microsoft Corporation

Module Name:

    small_object_allocator.cpp

Abstract:

    Small object allocator.

Author:

    Nikolaj bjorner (nbjorner) 2007-08-06.

Revision History:
    Leonardo de Moura (leonardo) 2011-04-27
    Rewrote/Simplified the allocator

--*/
#include "util/memory_manager.h"
#include "util/small_object_allocator.h"
#include "util/debug.h"
#include "util/util.h"
#include "util/vector.h"
#include<iomanip>
#ifdef Z3DEBUG
# include <iostream>
#endif

// Common object sizes optimized for Z3 usage patterns
const unsigned small_object_allocator::COMMON_SIZES[NUM_COMMON_POOLS] = {16, 32, 64, 128};


small_object_allocator::small_object_allocator(char const * id) {
    for (unsigned i = 0; i < NUM_SLOTS; i++) {
        m_chunks[i] = nullptr;
        m_free_list[i] = nullptr;
    }
    for (unsigned i = 0; i < NUM_COMMON_POOLS; i++) {
        m_pools[i] = nullptr;
    }
    DEBUG_CODE({
        m_id = id;
    });
    m_alloc_size = 0;
    m_pool_hits = 0;
    m_total_allocs = 0;
}

small_object_allocator::~small_object_allocator() {
    for (unsigned i = 0; i < NUM_SLOTS; i++) {
        chunk * c = m_chunks[i];
        while (c) {
            chunk * next = c->m_next;
            dealloc(c);
            c = next;
        }
    }
    // Clean up pools
    for (unsigned i = 0; i < NUM_COMMON_POOLS; i++) {
        pool_chunk* p = m_pools[i];
        while (p) {
            pool_chunk* next = p->m_next;
            dealloc(p);
            p = next;
        }
    }
    DEBUG_CODE({
        if (m_alloc_size > 0) {
            std::cerr << "Memory leak detected for small object allocator '" << m_id << "'. " << m_alloc_size << " bytes leaked" << std::endl;
        }
        // if (m_total_allocs > 0) {
        //     std::cerr << "Pool hit ratio for '" << m_id << "': " << get_pool_hit_ratio() * 100.0 << "%" << std::endl;
        // }
    });
}

void small_object_allocator::reset() {
    for (unsigned i = 0; i < NUM_SLOTS; i++) {
        chunk * c = m_chunks[i];
        while (c) {
            chunk * next = c->m_next;
            dealloc(c);
            c = next;
        }
        m_chunks[i] = nullptr;
        m_free_list[i] = nullptr;
    }
    // Reset pools
    for (unsigned i = 0; i < NUM_COMMON_POOLS; i++) {
        pool_chunk* p = m_pools[i];
        while (p) {
            pool_chunk* next = p->m_next;
            dealloc(p);
            p = next;
        }
        m_pools[i] = nullptr;
    }
    m_alloc_size = 0;
    m_pool_hits = 0;
    m_total_allocs = 0;
}

#define MASK ((1 << PTR_ALIGNMENT) - 1)

// Pool chunk implementation
void small_object_allocator::pool_chunk::init_free_list() {
    m_free_head = m_data;
    char* curr = m_data;
    for (unsigned i = 0; i < m_objects_per_chunk - 1; i++) {
        *(reinterpret_cast<void**>(curr)) = curr + m_obj_size;
        curr += m_obj_size;
    }
    *(reinterpret_cast<void**>(curr)) = nullptr;
}

void* small_object_allocator::pool_chunk::allocate() {
    if (m_free_head == nullptr) return nullptr;

    void* result = m_free_head;
    m_free_head = *(reinterpret_cast<void**>(m_free_head));
    m_free_count--;

#ifdef __builtin_prefetch
    if (m_free_head) __builtin_prefetch(m_free_head, 1, 3);
#endif

    return result;
}

void small_object_allocator::pool_chunk::deallocate(void* p) {
    *(reinterpret_cast<void**>(p)) = m_free_head;
    m_free_head = p;
    m_free_count++;
}

unsigned small_object_allocator::get_pool_index(size_t size) const {
    for (unsigned i = 0; i < NUM_COMMON_POOLS; i++) {
        if (size <= COMMON_SIZES[i]) return i;
    }
    return NUM_COMMON_POOLS; // Not found
}

small_object_allocator::pool_chunk* small_object_allocator::get_or_create_pool(unsigned pool_idx) {
    if (m_pools[pool_idx] == nullptr || m_pools[pool_idx]->m_free_head == nullptr) {
        // Create new pool chunk
        pool_chunk* new_pool = alloc(pool_chunk, COMMON_SIZES[pool_idx]);
        new_pool->m_next = m_pools[pool_idx];
        m_pools[pool_idx] = new_pool;
    }
    return m_pools[pool_idx];
}

void small_object_allocator::deallocate(size_t size, void * p) {
    if (size == 0) return;

#if defined(Z3DEBUG) && !defined(_WINDOWS)
    // Valgrind friendly
    memory::deallocate(p);
    return;
#endif
    SASSERT(m_alloc_size >= size);
    SASSERT(p);
    m_alloc_size -= size;

    if (size >= SMALL_OBJ_SIZE - (1 << PTR_ALIGNMENT)) {
        memory::deallocate(p);
        return;
    }

    // Try to deallocate from pools first
    unsigned pool_idx = get_pool_index(size);
    if (pool_idx < NUM_COMMON_POOLS) {
        // Find which pool chunk contains this pointer
        pool_chunk* pool = m_pools[pool_idx];
        while (pool != nullptr) {
            if (pool->contains(p)) {
                pool->deallocate(p);
                return;
            }
            pool = pool->m_next;
        }
    }

    // Fall back to slot-based deallocation
    unsigned slot_id = static_cast<unsigned>(size >> PTR_ALIGNMENT);
    if ((size & MASK) != 0)
        slot_id++;
    SASSERT(slot_id > 0);
    SASSERT(slot_id < NUM_SLOTS);
    *(reinterpret_cast<void**>(p)) = m_free_list[slot_id];
    m_free_list[slot_id] = p;
}


void * small_object_allocator::allocate(size_t size) {
    if (size == 0)
        return nullptr;

    m_total_allocs++; // Track allocation count

#if defined(Z3DEBUG) && !defined(_WINDOWS)
    // Valgrind friendly
    return memory::allocate(size);
#endif
    m_alloc_size += size;
    if (size >= SMALL_OBJ_SIZE - (1 << PTR_ALIGNMENT)) {
        return memory::allocate(size);
    }

    // Try pool allocation first for common sizes
    unsigned pool_idx = get_pool_index(size);
    if (pool_idx < NUM_COMMON_POOLS) {
        pool_chunk* pool = get_or_create_pool(pool_idx);
        void* result = pool->allocate();
        if (result != nullptr) {
            m_pool_hits++; // Track pool hits
            return result;
        }
    }

    // Fall back to original slot-based allocation
#ifdef Z3DEBUG
    size_t osize = size;
#endif
    unsigned slot_id = static_cast<unsigned>(size >> PTR_ALIGNMENT);
    if ((size & MASK) != 0)
        slot_id++;
    SASSERT(slot_id < NUM_SLOTS);
    SASSERT(slot_id > 0);
    if (m_free_list[slot_id] != nullptr) {
        void * r = m_free_list[slot_id];
        m_free_list[slot_id] = *(reinterpret_cast<void **>(r));
        return r;
    }
    chunk * c = m_chunks[slot_id];
    size = slot_id << PTR_ALIGNMENT;
    SASSERT(size >= osize);
    if (c != nullptr) {
        c->prefetch_next(); // Cache prefetch optimization
        char * new_curr = c->m_curr + size;
        if (new_curr < c->m_data + CHUNK_SIZE) {
            void * r = c->m_curr;
            c->m_curr = new_curr;
            return r;
        }
    }
    chunk * new_c = alloc(chunk);
    new_c->m_next = c;
    m_chunks[slot_id] = new_c;
    void * r = new_c->m_curr;
    new_c->m_curr += size;
    return r;
}

size_t small_object_allocator::get_wasted_size() const {
    size_t r = 0;

    // Count wasted space in slots
    for (unsigned slot_id = 0; slot_id < NUM_SLOTS; slot_id++) {
        size_t slot_obj_size = slot_id << PTR_ALIGNMENT;
        void ** ptr = reinterpret_cast<void **>(const_cast<small_object_allocator*>(this)->m_free_list[slot_id]);
        while (ptr != nullptr) {
            r += slot_obj_size;
            ptr = reinterpret_cast<void**>(*ptr);
        }
    }

    // Count wasted space in pools
    for (unsigned pool_idx = 0; pool_idx < NUM_COMMON_POOLS; pool_idx++) {
        pool_chunk* pool = const_cast<small_object_allocator*>(this)->m_pools[pool_idx];
        while (pool != nullptr) {
            r += pool->m_free_count * COMMON_SIZES[pool_idx];
            pool = pool->m_next;
        }
    }

    return r;
}

size_t small_object_allocator::get_num_free_objs() const {
    size_t r = 0;

    // Count free objects in slots
    for (unsigned slot_id = 0; slot_id < NUM_SLOTS; slot_id++) {
        void ** ptr = reinterpret_cast<void **>(const_cast<small_object_allocator*>(this)->m_free_list[slot_id]);
        while (ptr != nullptr) {
            r ++;
            ptr = reinterpret_cast<void**>(*ptr);
        }
    }

    // Count free objects in pools
    for (unsigned pool_idx = 0; pool_idx < NUM_COMMON_POOLS; pool_idx++) {
        pool_chunk* pool = const_cast<small_object_allocator*>(this)->m_pools[pool_idx];
        while (pool != nullptr) {
            r += pool->m_free_count;
            pool = pool->m_next;
        }
    }

    return r;
}

template<typename T>
struct ptr_lt {
    bool operator()(T * p1, T * p2) const { return p1 < p2; }
};

#define CONSOLIDATE_VB_LVL 20

void small_object_allocator::consolidate() {
    IF_VERBOSE(CONSOLIDATE_VB_LVL, 
               verbose_stream() << "(allocator-consolidate :wasted-size " << get_wasted_size()
               << " :memory " << std::fixed << std::setprecision(2) << 
               static_cast<double>(memory::get_allocation_size())/static_cast<double>(1024*1024) << ")" << std::endl;);
    ptr_vector<chunk> chunks;
    ptr_vector<char> free_objs;
    for (unsigned slot_id = 1; slot_id < NUM_SLOTS; slot_id++) {
        if (m_free_list[slot_id] == nullptr)
            continue;
        chunks.reset();
        free_objs.reset();
        chunk * c = m_chunks[slot_id];
        while (c != nullptr) {
            chunks.push_back(c);
            c = c->m_next;
        }
        char * ptr = static_cast<char*>(m_free_list[slot_id]);
        while (ptr != nullptr) {
            free_objs.push_back(ptr);
            ptr = *(reinterpret_cast<char**>(ptr));
        }
        unsigned obj_size = slot_id << PTR_ALIGNMENT;
        unsigned num_objs_per_chunk = CHUNK_SIZE / obj_size;
        if (free_objs.size() < num_objs_per_chunk)
            continue;
        SASSERT(!chunks.empty());
        std::sort(chunks.begin(), chunks.end(), ptr_lt<chunk>());
        std::sort(free_objs.begin(), free_objs.end(), ptr_lt<char>());
        chunk *   last_chunk = nullptr;
        void * last_free_obj = nullptr;
        unsigned chunk_idx = 0;
        unsigned obj_idx   = 0;
        unsigned num_chunks = chunks.size();
        unsigned num_objs   = free_objs.size();
        while (chunk_idx < num_chunks) {
            chunk * curr_chunk = chunks[chunk_idx];
            char *  curr_begin = curr_chunk->m_data;
            char *  curr_end   = curr_begin + CHUNK_SIZE;
            unsigned num_free_in_chunk = 0;
            unsigned saved_obj_idx = obj_idx;
            while (obj_idx < num_objs) {
                char * free_obj = free_objs[obj_idx];
                if (free_obj > curr_end)
                    break;
                obj_idx++;
                num_free_in_chunk++;
            }
            if (num_free_in_chunk == num_objs_per_chunk) {
                dealloc(curr_chunk);
            }
            else {
                curr_chunk->m_next = last_chunk;
                last_chunk = curr_chunk;
                for (unsigned i = saved_obj_idx; i < obj_idx; i++) {
                    // relink objects
                    void * free_obj = free_objs[i];
                    *(reinterpret_cast<void**>(free_obj)) = last_free_obj;
                    last_free_obj = free_obj;
                }
            }
            chunk_idx++;
        }
        m_chunks[slot_id]    = last_chunk;
        m_free_list[slot_id] = last_free_obj;
    }
    IF_VERBOSE(CONSOLIDATE_VB_LVL, 
               verbose_stream() << "(end-allocator-consolidate :wasted-size " << get_wasted_size() 
               << " :memory " << std::fixed << std::setprecision(2) 
               << static_cast<double>(memory::get_allocation_size())/static_cast<double>(1024*1024) << ")" << std::endl;);
}
