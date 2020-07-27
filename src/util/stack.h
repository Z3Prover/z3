/*++
Copyright (c) 2007 Microsoft Corporation

Module Name:

    stack.h

Abstract:
    Low level stack (aka stack-based allocator).

Author:

    Leonardo (leonardo) 2011-02-27

Notes:

--*/
#pragma once

#include "util/page.h"
#include "util/debug.h"

class stack {
    char *   m_curr_page;
    char *   m_curr_ptr;     //!< Next free space in the current page.
    char *   m_curr_end_ptr; //!< Point to the end of the current page.
    char *   m_free_pages;
    void store_mark(size_t m);
    void store_mark(void * ptr, bool external);
    size_t top_mark() const;
    void allocate_page(size_t mark);
    void * allocate_small(size_t size, bool external);
    void * allocate_big(size_t size);
public:
    stack();
    ~stack();
    void * allocate(size_t size) { return size < DEFAULT_PAGE_SIZE ? allocate_small(size, false) : allocate_big(size); }
    void deallocate();
    bool empty() const { return reinterpret_cast<size_t*>(m_curr_ptr)[-1] == 0; }
    void * top() const;
    void reset();
    template<typename T>
    void deallocate(T * ptr) { SASSERT(ptr == top()); ptr->~T(); deallocate(); }
};

inline void * operator new(size_t s, stack & r) { return r.allocate(s); }
inline void operator delete(void * ptr, stack & r) { SASSERT(ptr == r.top()); r.deallocate(); }

