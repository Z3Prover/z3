/*++
Copyright (c) 2011 Microsoft Corporation

Module Name:

    act_cache.h

Abstract:

    expr -> expr activity cache
    It maintains at most N unused entries

Author:

    Leonardo (leonardo) 2011-04-12

Notes:

--*/
#ifndef ACT_CACHE_H_
#define ACT_CACHE_H_

#include "ast/ast.h"
#include "util/obj_hashtable.h"
#include "util/chashtable.h"

class act_cache {
    ast_manager &        m_manager;
    typedef std::pair<expr*, unsigned> entry_t;
    struct entry_hash {
        unsigned operator()(entry_t const& e) const {
            return e.first->hash() + e.second;
        }
    };
    typedef cmap<entry_t, expr*, entry_hash, default_eq<entry_t> > map;
    map                  m_table;
    svector<entry_t>     m_queue; // recently created queue
    unsigned             m_qhead;
    unsigned             m_unused;
    unsigned             m_max_unused;

    void compress_queue();
    void init();
    void dec_refs();
    void del_unused();

public:
    act_cache(ast_manager & m);
    act_cache(ast_manager & m, unsigned max_unused);
    ~act_cache();
    void insert(expr * k, expr * v) { insert(k, 0, v); }
    expr * find(expr * k) { return find(k, 0); }
    void insert(expr * k, unsigned offset, expr * v);
    expr * find(expr * k, unsigned offset);
    void reset();
    void cleanup();
    unsigned size() const { return m_table.size(); }
    unsigned capacity() const { return m_table.capacity(); }
    bool empty() const { return m_table.empty(); }
    bool check_invariant() const;
    
};

#endif
