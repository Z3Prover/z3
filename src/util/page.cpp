/*++
Copyright (c) 2006 Microsoft Corporation

Module Name:

    page.cpp

Abstract:

    Goodies for manipulating pages of memory.

Author:

    Leonardo de Moura (leonardo) 2011-02-27.

Revision History:

--*/
#include "util/page.h"
#include "util/debug.h"

static void set_page_header(char * page, char * prev, bool default_page) {
    size_t header = reinterpret_cast<size_t>(prev) | static_cast<size_t>(default_page); 
    reinterpret_cast<size_t *>(page)[-1] = header;
    SASSERT(is_default_page(page) == default_page);
    SASSERT(prev_page(page) == prev);
}

static void set_page_header(char * page, char * prev, bool default_page, unsigned size) {
    reinterpret_cast<size_t *>(page)[-2] = size + PAGE_HEADER_SZ;
    set_page_header(page, prev, default_page);
}

static size_t page_size(char * page) {
  return reinterpret_cast<size_t *>(page)[-2];
}

static char * alloc_page(size_t s) { char * r = alloc_svect(char, s+PAGE_HEADER_SZ); return r + PAGE_HEADER_SZ; }

static void del_page(char * page) { dealloc_svect(page - PAGE_HEADER_SZ, page_size(page)); }

void del_pages(char * page) {
    while (page != nullptr) {
        char * prev = prev_page(page);
        del_page(page);
        page = prev;
    }
}

char * allocate_default_page(char * prev, char * & free_pages) {
    char * r;
    if (free_pages) {
        r = free_pages;
        free_pages = prev_page(free_pages);
    }
    else {
        r = alloc_page(DEFAULT_PAGE_SIZE);
    }
    set_page_header(r, prev, true, DEFAULT_PAGE_SIZE);
    return r;
}

char * allocate_page(char * prev, size_t sz) {
    char * r = alloc_page(sz);
    set_page_header(r, prev, false, sz);
    return r;
}

void recycle_page(char * p, char * & free_pages) {
    if (is_default_page(p)) {
        set_page_header(p, free_pages, true);
        free_pages = p;
    }
    else {
        del_page(p);
    }
}
