/*++
Copyright (c) 2006 Microsoft Corporation

Module Name:

    region.cpp

Abstract:

    Region/Arena memory manager

Author:

    Leonardo de Moura (leonardo) 2006-09-18.

Revision History:

--*/
#include "util/region.h"

#ifdef Z3DEBUG

void region::display_mem_stats(std::ostream & out) const {
    out << "num. objects:      " << m_chuncks.size() << "\n";
}

#else

#include "util/tptr.h"
#include "util/debug.h"
#include "util/memory_manager.h"
#include "util/page.h"

inline void region::allocate_page() {
    m_curr_page     = allocate_default_page(m_curr_page, m_free_pages);
    m_curr_ptr      = m_curr_page;
    m_curr_end_ptr  = end_of_default_page(m_curr_page);
}

region::region() {
    m_curr_page    = nullptr;
    m_curr_ptr     = nullptr;
    m_curr_end_ptr = nullptr;
    m_free_pages   = nullptr;
    m_mark         = nullptr;
    allocate_page();
}

region::~region() {
    del_pages(m_curr_page);
    del_pages(m_free_pages);
}

void * region::allocate(size_t size) {
    char * new_curr_ptr = m_curr_ptr + size;
    if (new_curr_ptr < m_curr_end_ptr) {
        char * result = m_curr_ptr;
        m_curr_ptr = ALIGN(char *, new_curr_ptr);
        return result;
    }
    else if (size < DEFAULT_PAGE_SIZE) {
        allocate_page(); 
        char * result = m_curr_ptr;
        m_curr_ptr += size;
        m_curr_ptr = ALIGN(char *, m_curr_ptr);
        return result;
    }
    else {
        // big page
        m_curr_page = ::allocate_page(m_curr_page, size);
        char * result = m_curr_page;
        allocate_page();
        return result;
    }
}

inline void region::recycle_curr_page() {
    char * prev = prev_page(m_curr_page);
    recycle_page(m_curr_page, m_free_pages);
    m_curr_page = prev;
}

void region::reset() {
    while (m_curr_page != nullptr) {
        recycle_curr_page();
    }
    SASSERT(m_curr_page == 0);
    m_curr_ptr     = nullptr;
    m_curr_end_ptr = nullptr;
    m_mark         = nullptr;
    allocate_page();
}

void region::push_scope() {
    char * curr_page = m_curr_page;
    char * curr_ptr  = m_curr_ptr;
    m_mark = new (*this) mark(curr_page, curr_ptr, m_mark);
}

void region::pop_scope() {
    SASSERT(m_mark);
    char * old_curr_page = m_mark->m_curr_page;
    SASSERT(is_default_page(old_curr_page));
    m_curr_ptr           = m_mark->m_curr_ptr;
    m_mark               = m_mark->m_prev_mark;
    while (m_curr_page != old_curr_page) {
        recycle_curr_page();
    }
    SASSERT(is_default_page(m_curr_page));
    m_curr_end_ptr       = end_of_default_page(m_curr_page);
}

void region::display_mem_stats(std::ostream & out) const {
    unsigned n = 0;
    char * page = m_curr_page;
    while (page != nullptr) {
        n++;
        page = prev_page(page);
    }
    out << "num. pages:      " << n << "\n";
}

#endif

