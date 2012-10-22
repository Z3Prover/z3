/*++
Copyright (c) 2011 Microsoft Corporation

Module Name:

    lru_cache.h

Abstract:

    expr -> expr LRU cache

Author:

    Leonardo (leonardo) 2011-04-12

Notes:

--*/
#ifndef _LRU_CACHE_H_
#define _LRU_CACHE_H_

#include"ast.h"

// #define LRU_CACHE_STATISTICS

#ifdef LRU_CACHE_STATISTICS
#define LCS_CODE(CODE) { CODE }
#else
#define LCS_CODE(CODE)
#endif

class lru_cache {
    struct cell {
        expr *  m_key;
        expr *  m_value;
        cell *  m_prev;
        cell *  m_next;
#ifdef LRU_CACHE_STATISTICS
        unsigned m_hits;
        unsigned m_birthday;
#endif
    };

    ast_manager & m_manager;
    cell *        m_table;
    cell *        m_head;
    unsigned      m_size;
    unsigned      m_max_size;
    unsigned      m_capacity;
    unsigned      m_num_deleted;
#ifdef LRU_CACHE_STATISTICS
    unsigned      m_time;
#endif

    static cell * allocate(unsigned capacity);
    static void deallocate(cell * table);
    static cell * copy_table(cell * old_head, cell * new_table, unsigned new_capacity);

    void del_least_used();
    void add_front(cell * c);
    void move_front(cell * c);
    void expand_table();
    void remove_deleted();
    void init();
    void dec_refs();
public:
    lru_cache(ast_manager & m);
    lru_cache(ast_manager & m, unsigned max_size);
    ~lru_cache();
    void insert(expr * k, expr * v);
    expr * find(expr * k);
    void reset();
    void cleanup();
    unsigned size() const { return m_size; }
    unsigned capacity() const { return m_capacity; }
    bool empty() const { return m_size == 0; }
    bool check_invariant() const;
};

#endif
