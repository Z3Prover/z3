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
#ifndef SMALL_OBJECT_ALLOCATOR_H_
#define SMALL_OBJECT_ALLOCATOR_H_

#include"machine.h"
#include"debug.h"

class small_object_allocator {
    static const unsigned CHUNK_SIZE     = (8192 - sizeof(void*)*2);
    static const unsigned SMALL_OBJ_SIZE = 256;
    static const unsigned NUM_SLOTS      = (SMALL_OBJ_SIZE >> PTR_ALIGNMENT);
    struct chunk {
        chunk * m_next;
        char  * m_curr;
        char    m_data[CHUNK_SIZE];
        chunk():m_curr(m_data) {}
    };
    chunk *     m_chunks[NUM_SLOTS];
    void  *     m_free_list[NUM_SLOTS];
    size_t      m_alloc_size;
#ifdef Z3DEBUG
    char const * m_id;
#endif
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
};

inline void * operator new(size_t s, small_object_allocator & r) { return r.allocate(s); }
inline void * operator new[](size_t s, small_object_allocator & r) { return r.allocate(s); }
inline void operator delete(void * p, small_object_allocator & r) { UNREACHABLE(); }
inline void operator delete[](void * p, small_object_allocator & r) { UNREACHABLE(); }

#endif /* SMALL_OBJECT_ALLOCATOR_H_ */

