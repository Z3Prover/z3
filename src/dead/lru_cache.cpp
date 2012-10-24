/*++
Copyright (c) 2011 Microsoft Corporation

Module Name:

    lru_cache.cpp

Abstract:

    expr -> expr LRU cache

Author:

    Leonardo (leonardo) 2011-04-12

Notes:

--*/
#include"lru_cache.h"
#include"ast_ll_pp.h"

#define MIN_MAX_SIZE     1024
#define INITIAL_CAPACITY 128

lru_cache::cell * lru_cache::allocate(unsigned capacity) {
    cell * mem = static_cast<cell*>(memory::allocate(sizeof(cell) * capacity));
    memset(mem, 0, sizeof(cell)*capacity);
    return mem;
}

void lru_cache::deallocate(cell * table) {
    memory::deallocate(table);
}

lru_cache::cell * lru_cache::copy_table(cell * old_head, cell * new_table, unsigned new_capacity) {
    SASSERT(old_head);
    cell * it = old_head;
    cell * new_head = 0;
    cell * prev = 0;
    do {
        expr * k       = it->m_key;
        unsigned h     = k->hash();
        unsigned mask  = new_capacity - 1;
        unsigned idx   = h & mask;
        
        cell * begin = new_table + idx;
        cell * end   = new_table + new_capacity;
        cell * curr  = begin;

        for (; curr != end; ++curr) {
            if (curr->m_key == 0) {
                curr->m_key   = k;
                curr->m_value = it->m_value;
                LCS_CODE(curr->m_hits = it->m_hits;);
                LCS_CODE(curr->m_birthday = it->m_birthday;);
                if (prev == 0) {
                    new_head = curr;
                }
                else {
                    prev->m_next = curr;
                    curr->m_prev = prev;
                }
                goto end;
            }
        }
        for (curr = new_table; curr != begin; ++curr) {
            if (curr->m_key == 0) {
                curr->m_key   = k;
                curr->m_value = it->m_value;
                SASSERT(prev != 0);
                prev->m_next = curr;
                curr->m_prev = prev;
            }
            goto end;
        }
        UNREACHABLE();
    end:
        prev = curr;
        it = it->m_next;
    }
    while (it != old_head);
    prev->m_next     = new_head;
    new_head->m_prev = prev;
    return new_head;
}

void lru_cache::expand_table() {
    SASSERT(m_head);
    unsigned new_capacity = m_capacity * 2;
    TRACE("lru_cache", tout << "expanding table new_capacity: " << new_capacity << "\n";);
    cell *   new_table    = allocate(new_capacity);
    m_head     = copy_table(m_head, new_table, new_capacity);
    deallocate(m_table);
    m_table    = new_table;
    m_capacity = new_capacity;
    m_num_deleted = 0;
    SASSERT(check_invariant());
}

void lru_cache::remove_deleted() {
    SASSERT(m_head);
    TRACE("lru_cache", tout << "removing deleted entries\n";);
    cell *   new_table    = allocate(m_capacity);
    m_head     = copy_table(m_head, new_table, m_capacity);
    deallocate(m_table);
    m_table    = new_table;
    m_num_deleted = 0;
    SASSERT(check_invariant());
}

void lru_cache::init() {
    if (m_max_size < MIN_MAX_SIZE)
        m_max_size = MIN_MAX_SIZE;
    m_size = 0;
    m_capacity = INITIAL_CAPACITY;
    m_table = allocate(m_capacity);
    m_head  = 0;
    m_num_deleted = 0;
}

lru_cache::lru_cache(ast_manager & m):
    m_manager(m),
    m_max_size(m.get_num_asts() * 100) {
    init();
    TRACE("lru_cache", tout << "new lru cache, max-size: " << m_max_size << "\n";);
}
 
lru_cache::lru_cache(ast_manager & m, unsigned max_size):
    m_manager(m),
    m_max_size(max_size) {
    init();
}

void lru_cache::dec_refs() {
    if (m_head) {
        cell * curr = m_head;
#ifdef Z3DEBUG
        unsigned sz = 0;
#endif
        do {
            m_manager.dec_ref(curr->m_key);
            m_manager.dec_ref(curr->m_value);
            curr = curr->m_next;
            DEBUG_CODE(sz++;);
        }
        while (curr != m_head);
        SASSERT(sz == m_size);
    }
}
 
lru_cache::~lru_cache() {
    TRACE("lru_cache", tout << "destructor invoked size: " << m_size << ", m_head: " << m_head << "\n";);
    LCS_CODE({
        if (m_head) {
            unsigned used = 0;
            cell * curr = m_head;
            do {
                if (curr->m_hits > 0)
                    used++;
                curr = curr->m_next;
            }
            while (curr != m_head);
            verbose_stream() << "[lru_cache] num-used: " << used << " size: " << m_size << "\n";
        }
    });
    SASSERT(check_invariant());
    dec_refs();
    deallocate(m_table);
}

void lru_cache::del_least_used() {
    SASSERT(m_head);
    SASSERT(m_size >= 2);
    cell * c = m_head->m_prev;
    TRACE("lru_cache", tout << "del least used: " << mk_bounded_pp(c->m_key, m_manager, 3) << "\n";);
    LCS_CODE({
        static unsigned non_zero = 0;
        static unsigned long long total_hits;
        static unsigned counter = 0;
        if (c->m_hits > 0) {
            counter++;
            total_hits += c->m_hits;
            non_zero++;
            if (non_zero % 1000 == 0)
                verbose_stream() << "[lru_cache] cell with non-zero hits was deleted: " << non_zero << " avg: " << ((double)total_hits/(double) counter) << std::endl;
        }
    });
    SASSERT(c->m_prev != c);
    SASSERT(c->m_next != c);
    m_manager.dec_ref(c->m_key);
    m_manager.dec_ref(c->m_value);
    c->m_prev->m_next = c->m_next;
    c->m_next->m_prev = c->m_prev;
    SASSERT(m_head->m_prev == c->m_prev);
    c->m_key  = reinterpret_cast<expr*>(1);
    c->m_prev = 0;
    c->m_next = 0;
    m_size--;
    m_num_deleted++;
    CASSERT("lru_cache", check_invariant());
    if (m_num_deleted * 3 > m_capacity)
        remove_deleted();
}

void lru_cache::add_front(cell * c) {
    SASSERT(c->m_next == 0);
    SASSERT(c->m_prev == 0);
    if (m_head == 0) {
        c->m_next = c;
        c->m_prev = c;
        m_head    = c;
    }
    else {
        c->m_prev = m_head->m_prev;
        c->m_next = m_head;
        m_head->m_prev->m_next = c;
        m_head->m_prev = c;
        m_head = c;
    }
    CASSERT("lru_cache", check_invariant());
    SASSERT(m_head == c);
}

void lru_cache::move_front(cell * c) {
    SASSERT(m_head);
    SASSERT(c->m_next);
    SASSERT(c->m_prev);
    if (m_head != c) {
        c->m_prev->m_next = c->m_next;
        c->m_next->m_prev = c->m_prev;
        
        c->m_prev = m_head->m_prev;
        c->m_next = m_head;
        
        m_head->m_prev->m_next = c;
        m_head->m_prev         = c;
        
        m_head = c;
    }
    CASSERT("lru_cache", check_invariant());
    SASSERT(m_head == c);
}

void lru_cache::insert(expr * k, expr * v) {
    LCS_CODE(m_time++;);
    if (m_size == m_max_size)
        del_least_used();
    else if (m_size * 2 > m_capacity)
        expand_table();
    SASSERT(m_size < m_max_size);
    unsigned h     = k->hash();
    unsigned mask  = m_capacity - 1;
    unsigned idx   = h & mask;

    cell * begin = m_table + idx;
    cell * end   = m_table + m_capacity;
    cell * curr  = begin;
    cell * del_cell = 0;

#define INSERT_LOOP()                                           \
        if (curr->m_key == 0) {                                 \
            cell * new_cell;                                    \
            if (del_cell) {                                     \
                new_cell = del_cell;                            \
                m_num_deleted--;                                \
            }                                                   \
            else {                                              \
                new_cell = curr;                                \
            }                                                   \
            m_manager.inc_ref(k);                               \
            m_manager.inc_ref(v);                               \
            new_cell->m_key   = k;                              \
            new_cell->m_value = v;                              \
            LCS_CODE(new_cell->m_hits = 0;);                    \
            LCS_CODE(new_cell->m_birthday = m_time;);           \
            m_size++;                                           \
            add_front(new_cell);                                \
            return;                                             \
        }                                                       \
        if (curr->m_key == reinterpret_cast<expr*>(1)) {        \
            del_cell = curr;                                    \
            continue;                                           \
        }                                                       \
        if (curr->m_key == k) {                                 \
            m_manager.inc_ref(v);                               \
            m_manager.dec_ref(curr->m_value);                   \
            curr->m_value = v;                                  \
            LCS_CODE(curr->m_hits = 0;);                        \
            LCS_CODE(curr->m_birthday = m_time;);               \
            move_front(curr);                                   \
            return;                                             \
        }

    for (; curr != end; ++curr) {
        INSERT_LOOP();
    }
    for (curr = m_table; curr != begin; ++curr) {
        INSERT_LOOP();
    } 
    UNREACHABLE();
}

expr * lru_cache::find(expr * k) {
    unsigned h     = k->hash();
    unsigned mask  = m_capacity - 1;
    unsigned idx   = h & mask;

#ifdef LRU_CACHE_STATISTICS
    static unsigned long long total_age = 0;
    static unsigned long long max_time = 0;
    static unsigned counter = 0;
#define COLLECT()                                                                                                                                       \
    if (curr->m_hits == 0) {                                                                                                                            \
        counter ++;                                                                                                                                     \
        unsigned age = m_time - curr->m_birthday;                                                                                                       \
        if (age > max_time)                                                                                                                             \
            max_time = age;                                                                                                                             \
        total_age += age;                                                                                                                               \
        if (counter % 1000 == 0)                                                                                                                        \
            verbose_stream() << "[lru_cache] avg time for first hit: " << ((double) total_age / (double) counter) << " max time: " << max_time << "\n";        \
    }
#endif    

    cell * begin = m_table + idx;
    cell * end   = m_table + m_capacity;
    cell * curr  = begin;
    for (; curr != end; ++curr) {
        if (curr->m_key == k) {
            // LCS_CODE(COLLECT());
            LCS_CODE(if (curr->m_hits == 0 && m_time - curr->m_birthday >= 5000) return 0;)
            LCS_CODE(curr->m_hits++;);
            move_front(curr);
            return curr->m_value;
        }
        if (curr->m_key == 0) 
            return 0;
    }
    for (curr = m_table; curr != begin; ++curr) {
        if (curr->m_key == k) {
            // LCS_CODE(COLLECT());
            LCS_CODE(curr->m_hits++;);
            LCS_CODE(if (curr->m_hits == 0 && m_time - curr->m_birthday >= 5000) return 0;);
            move_front(curr);
            return curr->m_value;
        }
        if (curr->m_key == 0) 
            return 0;
    }
    return 0;
}

void lru_cache::reset() {
    TRACE("lru_cache", tout << "reset... m_size: " << m_size << "\n";);
    LCS_CODE(m_time = 0;);
    if (m_head) {
        cell * curr = m_head;
#ifdef Z3DEBUG
        unsigned sz = 0;
#endif
        do {
            m_manager.dec_ref(curr->m_key);
            m_manager.dec_ref(curr->m_value);
            cell * next = curr->m_next;
            curr->m_key   = 0;
            curr->m_value = 0;
            curr->m_next  = 0;
            curr->m_prev  = 0;
            LCS_CODE(curr->m_hits = 0;);
            LCS_CODE(curr->m_birthday = 0;);
            curr = next;
            DEBUG_CODE(sz++;);
        }
        while (curr != m_head);
        SASSERT(sz == m_size);
        m_head = 0;
        m_size = 0;
        SASSERT(check_invariant());
    }
}
 
void lru_cache::cleanup() {
    dec_refs();
    deallocate(m_table);
    m_capacity    = INITIAL_CAPACITY;
    m_table       = allocate(m_capacity); 
    m_head        = 0;
    m_size        = 0;
    m_num_deleted = 0;
}

bool lru_cache::check_invariant() const {
    SASSERT(m_size <= m_max_size);
    cell * begin         = m_table;
    cell * end           = m_table + m_capacity;
    unsigned sz          = 0;
    if (m_head) {
        cell * curr  = m_head;
        do {
            sz++;
            SASSERT(curr->m_key != 0 && curr->m_key != reinterpret_cast<expr*>(1));
            SASSERT(curr->m_next->m_prev == curr);
            SASSERT(curr->m_prev->m_next == curr);
            SASSERT(curr < end);
            SASSERT(curr >= begin);
            curr = curr->m_next;
        }
        while (curr != m_head);
    }
    SASSERT(m_size == sz);
    sz = 0;
    unsigned num_deleted = 0;
    for (cell * it = begin; it != end; it++) {
        if (it->m_key == reinterpret_cast<expr*>(1)) {
            num_deleted++;
            continue;
        }
        if (it->m_key != 0) {
            sz++;
        }
    }
    SASSERT(m_size == sz);
    SASSERT(m_num_deleted == num_deleted);
    return true;
}
