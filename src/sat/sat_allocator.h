/*++
Copyright (c) 2018 Microsoft Corporation

Module Name:

    sat_allocator.h

Abstract:

    Small object allocator suitable for clauses

Author:

    Nikolaj bjorner (nbjorner) 2018-04-26.

Revision History:
--*/

#ifndef SAT_ALLOCATOR_H_
#define SAT_ALLOCATOR_H_

#include "util/vector.h"
#include "util/machine.h"

class sat_allocator {
    static const unsigned CHUNK_SIZE     = (1 << 16) - sizeof(char*);
    static const unsigned SMALL_OBJ_SIZE = 512;
    static const unsigned MASK = ((1 << PTR_ALIGNMENT) - 1);
    static const unsigned NUM_FREE = 1 + (SMALL_OBJ_SIZE >> PTR_ALIGNMENT);
    struct chunk {
        char  * m_curr;
        char    m_data[CHUNK_SIZE];
        chunk():m_curr(m_data) {}
    };
    char const *              m_id;
    size_t                    m_alloc_size;
    ptr_vector<chunk>         m_chunks;
    void *                    m_chunk_ptr;
    ptr_vector<void>          m_free[NUM_FREE];

    unsigned align_size(size_t sz) const {
        return  free_slot_id(sz) << PTR_ALIGNMENT;
    }
    unsigned free_slot_id(size_t size) const {
        return (static_cast<unsigned>(size >> PTR_ALIGNMENT) + ((0 != (size & MASK)) ? 1u : 0u));
    }
public:
    sat_allocator(char const * id = "unknown"): m_id(id), m_alloc_size(0), m_chunk_ptr(nullptr) {}
    ~sat_allocator() { reset(); }
    void reset() {
        for (chunk * ch : m_chunks) dealloc(ch);
        m_chunks.reset();
        for (unsigned i = 0; i < NUM_FREE; ++i) m_free[i].reset();
        m_alloc_size = 0;
        m_chunk_ptr = nullptr;
    }
    void * allocate(size_t size) {
        m_alloc_size += size;
        if (size >= SMALL_OBJ_SIZE) {
            return memory::allocate(size);
        }
        unsigned slot_id = free_slot_id(size);
        if (!m_free[slot_id].empty()) {
            void* result = m_free[slot_id].back();
            m_free[slot_id].pop_back();
            return result;
        }
        if (m_chunks.empty()) {
            m_chunks.push_back(alloc(chunk));
            m_chunk_ptr = m_chunks.back();
        }
        
        unsigned sz = align_size(size);
        if ((char*)m_chunk_ptr + sz > (char*)m_chunks.back() + CHUNK_SIZE) {
            m_chunks.push_back(alloc(chunk));
            m_chunk_ptr = m_chunks.back();            
        }
        void * result = m_chunk_ptr;
        m_chunk_ptr = (char*)m_chunk_ptr + sz;
        return result;
    }

    void deallocate(size_t size, void * p) {
        m_alloc_size -= size;
        if (size >= SMALL_OBJ_SIZE) {
            memory::deallocate(p);
        }
        else {
            m_free[free_slot_id(size)].push_back(p);
        }
    }
    size_t get_allocation_size() const { return m_alloc_size; }

    char const* id() const { return m_id; }
};

inline void * operator new(size_t s, sat_allocator & r) { return r.allocate(s); }
inline void * operator new[](size_t s, sat_allocator & r) { return r.allocate(s); }
inline void operator delete(void * p, sat_allocator & r) { UNREACHABLE(); }
inline void operator delete[](void * p, sat_allocator & r) { UNREACHABLE(); }

#endif /* SAT_ALLOCATOR_H_ */

