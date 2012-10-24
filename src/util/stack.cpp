/*++
Copyright (c) 2007 Microsoft Corporation

Module Name:

    stack.cpp

Abstract:
    Low level stack (aka stack-based allocator).

Author:

    Leonardo (leonardo) 2011-02-27

Notes:

--*/
#include"stack.h"
#include"page.h"
#include"tptr.h"

inline void stack::store_mark(size_t m) {
    reinterpret_cast<size_t*>(m_curr_ptr)[0] = m;
    m_curr_ptr += sizeof(size_t);
}

inline size_t stack::top_mark() const {
    return reinterpret_cast<size_t*>(m_curr_ptr)[-1];
}

inline size_t ptr2mark(void * ptr, bool external) {
    return reinterpret_cast<size_t>(ptr) | static_cast<size_t>(external);
}

#define MASK (static_cast<size_t>(-1) - 1)

inline char * mark2ptr(size_t m) {
    return reinterpret_cast<char *>(m & MASK);
}

inline bool external_ptr(size_t m) {
    return static_cast<bool>(m & 1);
}

inline void stack::allocate_page(size_t m) {
    m_curr_page     = allocate_default_page(m_curr_page, m_free_pages);
    m_curr_ptr      = m_curr_page;
    m_curr_end_ptr  = end_of_default_page(m_curr_page);
    store_mark(m);
}

inline void stack::store_mark(void * ptr, bool external) {
    SASSERT(m_curr_ptr < m_curr_end_ptr || m_curr_ptr == m_curr_end_ptr); // mem is aligned
    if (m_curr_ptr + sizeof(size_t) > m_curr_end_ptr) {
        SASSERT(m_curr_ptr == m_curr_end_ptr);
        // doesn't fit in the current page
        allocate_page(ptr2mark(ptr, external));
    }
    else {
        store_mark(ptr2mark(ptr, external));
    }
}

stack::stack() {
    m_curr_page    = 0;
    m_curr_ptr     = 0;
    m_curr_end_ptr = 0;
    m_free_pages   = 0;
    allocate_page(0);
    SASSERT(empty());
}

stack::~stack() {
    reset();
    del_pages(m_curr_page);
    del_pages(m_free_pages);
}

void stack::reset() {
    while(!empty())
        deallocate();
}

void * stack::top() const {
    SASSERT(!empty());
    size_t m = top_mark();
    void * r = mark2ptr(m);
    if (external_ptr(m)) 
        r = reinterpret_cast<void**>(r)[0];
    return r;
}

void * stack::allocate_small(size_t size, bool external) {
    SASSERT(size < DEFAULT_PAGE_SIZE);
    char * new_curr_ptr = m_curr_ptr + size;
    char * result;
    if (new_curr_ptr < m_curr_end_ptr) {
        result = m_curr_ptr;
        m_curr_ptr = ALIGN(char *, new_curr_ptr);
    }
    else {
        allocate_page(top_mark()); 
        result = m_curr_ptr;
        m_curr_ptr += size;
        m_curr_ptr = ALIGN(char *, m_curr_ptr);
    }
    store_mark(result, external);
    SASSERT(m_curr_ptr > m_curr_page);
    SASSERT(m_curr_ptr <= m_curr_end_ptr);
    return result;
}

void * stack::allocate_big(size_t size) {
    char * r   = alloc_svect(char, size);
    void * mem = allocate_small(sizeof(char*), true);
    reinterpret_cast<char**>(mem)[0] = r;
    SASSERT(m_curr_ptr > m_curr_page);
    SASSERT(m_curr_ptr <= m_curr_end_ptr);
    return r;
}
    
void stack::deallocate() {
    SASSERT(m_curr_ptr > m_curr_page);
    SASSERT(m_curr_ptr <= m_curr_end_ptr);
    size_t m = top_mark();
    SASSERT(m != 0);
    if (m_curr_ptr == m_curr_page + sizeof(size_t)) {
        // mark is in the beginning of the page
        char * prev = prev_page(m_curr_page);
        recycle_page(m_curr_page, m_free_pages);
        m_curr_page    = prev;
        m_curr_ptr     = mark2ptr(m);
        m_curr_end_ptr = end_of_default_page(m_curr_page);
        SASSERT(m_curr_ptr >  m_curr_page);
        SASSERT(m_curr_ptr <= m_curr_end_ptr);
    }
    else {
        // mark is in the middle of the page
        m_curr_ptr = mark2ptr(m);
        SASSERT(m_curr_ptr < m_curr_end_ptr);
    }
    if (external_ptr(m)) {
        dealloc_svect(reinterpret_cast<char**>(m_curr_ptr)[0]);
    }
    SASSERT(m_curr_ptr > m_curr_page);
}


