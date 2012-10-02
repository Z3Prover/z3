/*++
Copyright (c) 2006 Microsoft Corporation

Module Name:

    page.h

Abstract:

    Goodies for manipulating pages of memory.

Author:

    Leonardo de Moura (leonardo) 2011-02-27.

Revision History:

--*/
#ifndef _PAGE_H_
#define _PAGE_H_

#include"memory_manager.h"

#define PAGE_HEADER_SZ sizeof(size_t)
#define DEFAULT_PAGE_SIZE (8192 - PAGE_HEADER_SZ)
#define PAGE_HEADER_MASK (static_cast<size_t>(-1) - 1)

inline char * prev_page(char * page) {
    size_t tagged_ptr = reinterpret_cast<size_t *>(page)[-1];
    return reinterpret_cast<char *>(tagged_ptr & PAGE_HEADER_MASK);
}
inline bool is_default_page(char * page) {
    size_t tagged_ptr = reinterpret_cast<size_t *>(page)[-1];
    return static_cast<bool>(tagged_ptr & 1);
}
inline char * end_of_default_page(char * p) { return p + DEFAULT_PAGE_SIZE; }
void del_pages(char * page);
char * allocate_default_page(char * prev, char * & free_pages);
char * allocate_page(char * prev, size_t sz);
void recycle_page(char * p, char * & free_pages);

#endif
