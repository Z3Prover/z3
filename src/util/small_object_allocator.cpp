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

small_object_allocator::small_object_allocator(char const * id) {
    for (unsigned i = 0; i < NUM_SLOTS; i++) {
        m_chunks[i] = nullptr;
        m_free_list[i] = nullptr;
    }
    DEBUG_CODE({
        m_id = id;
    });
    m_alloc_size = 0;
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
    DEBUG_CODE({
        if (m_alloc_size > 0) {
            std::cerr << "Memory leak detected for small object allocator '" << m_id << "'. " << m_alloc_size << " bytes leaked" << std::endl;
        }
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
    m_alloc_size = 0;
}

#define MASK ((1 << PTR_ALIGNMENT) - 1)


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
    unsigned slot_id = static_cast<unsigned>(size >> PTR_ALIGNMENT);
    if ((size & MASK) != 0)
        slot_id++;
    SASSERT(slot_id > 0);
    SASSERT(slot_id < NUM_SLOTS);
    *(reinterpret_cast<void**>(p)) = m_free_list[slot_id];
    m_free_list[slot_id] = p;
}


void * small_object_allocator::allocate(size_t size) {
    if (size == 0) return nullptr;

#if defined(Z3DEBUG) && !defined(_WINDOWS)
    // Valgrind friendly
    return memory::allocate(size);
#endif
    m_alloc_size += size;
    if (size >= SMALL_OBJ_SIZE - (1 << PTR_ALIGNMENT)) {
        return memory::allocate(size);
    }
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
    for (unsigned slot_id = 0; slot_id < NUM_SLOTS; slot_id++) {
        size_t slot_obj_size = slot_id << PTR_ALIGNMENT;
        void ** ptr = reinterpret_cast<void **>(const_cast<small_object_allocator*>(this)->m_free_list[slot_id]);
        while (ptr != nullptr) {
            r += slot_obj_size;
            ptr = reinterpret_cast<void**>(*ptr);
        }
    }
    return r;
}

size_t small_object_allocator::get_num_free_objs() const {
    size_t r = 0;
    for (unsigned slot_id = 0; slot_id < NUM_SLOTS; slot_id++) {
        void ** ptr = reinterpret_cast<void **>(const_cast<small_object_allocator*>(this)->m_free_list[slot_id]);
        while (ptr != nullptr) {
            r ++;
            ptr = reinterpret_cast<void**>(*ptr);
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
