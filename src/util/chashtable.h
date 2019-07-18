/*++
Copyright (c) 2011 Microsoft Corporation

Module Name:

    chashtable.h

Abstract:

    Hashtable with chaining.  

    The performance of the hashtable in hashtable.h deteriorates if
    there is a huge number of deletions. In this case, the hashtable
    starts to contain many cells marked as deleted, and insertion/deletion
    start to suffer.
    
    The hashtable defined in this class addresses this problem by using
    chaining. Of course, there is the cost of storing the link to the next
    cell.
    
Author:

    Leonardo de Moura (leonardo) 2011-04-14.

Revision History:

--*/
#ifndef CHASHTABLE_H_
#define CHASHTABLE_H_

#include "util/memory_manager.h"
#include "util/debug.h"
#include "util/trace.h"
#include "util/tptr.h"
#include "util/util.h"
#ifdef Z3DEBUG
#include "util/hashtable.h"
#endif

#define CH_STATISTICS

#ifdef CH_STATISTICS
#define CHS_CODE(CODE) { CODE }
#else
#define CHS_CODE(CODE) 
#endif

template<typename T, typename HashProc, typename EqProc>
class chashtable : private HashProc, private EqProc {
public:
    static const unsigned default_init_slots  = 8;
    static const unsigned default_init_cellar = 2;

protected:
    struct cell {
        cell *  m_next;
        T       m_data;
        cell():m_next(reinterpret_cast<cell*>(1)) {}
        bool is_free() const { return GET_TAG(m_next) == 1; }
        void mark_free() { m_next = TAG(cell*, m_next, 1); }
        void unmark_free() { m_next = UNTAG(cell*, m_next); }
    };
    
    cell *    m_table;         // array of cells.
    unsigned  m_capacity;      // size of the array of cells.
    unsigned  m_init_slots; 
    unsigned  m_init_cellar;   
    unsigned  m_slots;         // m_slots < m_capacity, and m_slots is a power of two, the cells [m_slots, m_capacity) are used for chaining. 
    unsigned  m_used_slots;    // m_used_slots <= m_slots (number of used slots).
    unsigned  m_size;          // number of occupied cells.
#ifdef CH_STATISTICS
    unsigned  m_collisions;
#endif
    cell *    m_next_cell;   
    cell *    m_free_cell;   
    cell *    m_tofree_cell;
    
    unsigned get_hash(T const & d) const { return HashProc::operator()(d); }
    bool equals(T const & e1, T const & e2) const { return EqProc::operator()(e1, e2); }

    static cell * alloc_table(unsigned sz) {
        return alloc_vect<cell>(sz); 
    }
    
    void delete_table() {
        dealloc_vect(m_table, m_capacity);
    }
    
    // Return the next free cell in the cellar, and the number of used slots
    // Return 0 if the cellar is too small (unlikely but it might happen with a bad hash)
    cell * copy_table(cell * source, unsigned source_slots, unsigned source_capacity, 
                      cell * target, unsigned target_slots, unsigned target_capacity,
                      unsigned & used_slots) {
        TRACE("chashtable", tout << "copy_table...\n";);
        SASSERT(target_slots >= source_slots);
        SASSERT(target_capacity >= source_capacity);
        unsigned target_mask  = target_slots - 1;
        used_slots   = 0;
        cell *  source_end    = source + source_slots;
        cell *  target_cellar = target + target_slots;
        cell *  target_end    = target + target_capacity;
        for (cell * source_it = source; source_it != source_end; ++source_it) {
            if (!source_it->is_free()) {
                cell * list_it = source_it;
                do {
                    unsigned h    = get_hash(list_it->m_data);
                    unsigned idx  = h & target_mask;
                    cell * target_it = target + idx;
                    SASSERT(target_it >= target);
                    SASSERT(target_it < target + target_slots);
                    if (target_it->is_free()) {
                        target_it->m_data = list_it->m_data;
                        target_it->m_next = nullptr;
                        used_slots++;
                    }
                    else {
                        SASSERT((get_hash(target_it->m_data) & target_mask) == idx);
                        if (target_cellar == target_end)
                            return nullptr; // the cellar is too small...
                        SASSERT(target_cellar >= target + target_slots);
                        SASSERT(target_cellar < target_end);
                        *target_cellar    = *target_it;
                        target_it->m_data = list_it->m_data;
                        target_it->m_next = target_cellar;
                        target_cellar++;
                    }
                    SASSERT(!target_it->is_free());
                    list_it = list_it->m_next;
                }
                while (list_it != nullptr);
            }
        }
#if 0
        TRACE("chashtable", 
              for (unsigned i = 0; i < source_capacity; i++) {
                  tout << i << ":[";
                  if (source[i].m_next == 0)
                      tout << "null";
                  else if (source[i].m_next == reinterpret_cast<cell*>(1))
                      tout << "X";
                  else
                      tout << (source[i].m_next - source);
                  tout << ", " << source[i].m_data << "]\n";
              }
              tout << "\n";
              for (unsigned i = 0; i < target_capacity; i++) {
                  tout << i << ":[";
                  if (target[i].m_next == 0)
                      tout << "null";
                  else if (target[i].m_next == reinterpret_cast<cell*>(1))
                      tout << "X";
                  else
                      tout << (target[i].m_next - target);
                  tout << ", " << target[i].m_data << "]\n";
              }
              tout << "\n";);
#endif
        return target_cellar;
    }
    
    void expand_table() {
        unsigned curr_cellar  = (m_capacity - m_slots);
        unsigned new_slots    = m_slots * 2;
        unsigned new_cellar   = curr_cellar * 2;
        while (true) {
            unsigned new_capacity = new_slots + new_cellar;
            cell * new_table      = alloc_table(new_capacity);
            cell * next_cell      = copy_table(m_table, m_slots, m_capacity,
                                               new_table, new_slots, new_capacity,
                                               m_used_slots);
            if (next_cell != nullptr) {
                delete_table();
                m_table      = new_table;
                m_capacity   = new_capacity;
                m_slots      = new_slots;
                m_next_cell  = next_cell;
                m_free_cell  = nullptr;
                m_tofree_cell = nullptr;
                CASSERT("chashtable", check_invariant());
                return;
            }
            dealloc_vect(new_table, new_capacity);
            new_cellar *= 2;
        }
    }

    bool has_free_cells() const {
        return m_free_cell != nullptr || m_next_cell < m_table + m_capacity;
    }

    cell * get_free_cell() {
        if (m_free_cell != nullptr) {
            cell * c    = m_free_cell;
            m_free_cell = c->m_next;
            return c;
        }
        else {
            cell * c = m_next_cell;
            m_next_cell++;
            return c;
        }
    }

    void recycle_cell(cell * c) {
        // c is in the cellar
        SASSERT(c >= m_table + m_slots);
        SASSERT(c < m_table + m_capacity);
        c->m_next   = m_free_cell;
        m_free_cell = c;
    }

    void push_recycle_cell(cell* c) {
        SASSERT(c < m_table + m_capacity);
        c->m_next = m_tofree_cell;
        m_tofree_cell = c;
    }

    void init(unsigned slots, unsigned cellar) {
        m_capacity   = slots + cellar;
        m_table      = alloc_table(m_capacity);
        m_slots      = slots;
        m_used_slots = 0;
        m_size       = 0;
        m_next_cell  = m_table + slots;
        m_free_cell  = nullptr;
        m_tofree_cell = nullptr;
    }

public:
    chashtable(HashProc const & h = HashProc(),
               EqProc const & e = EqProc(),
               unsigned init_slots  = default_init_slots,
               unsigned init_cellar = default_init_cellar):
        HashProc(h),
        EqProc(e) {
        SASSERT(is_power_of_two(init_slots));
        SASSERT(init_cellar > 0);
        m_init_slots = init_slots;
        m_init_cellar = init_cellar;
        init(m_init_slots, m_init_cellar);
        CHS_CODE(m_collisions = 0;);
    }

    ~chashtable() {
#if 0
        cell * it  = m_table;
        cell * end = m_table + m_slots;
        verbose_stream() << "[chashtable] free slots: ";
        for (; it != end; ++it) {
            if (it->is_free())
                verbose_stream() << (it - m_table) << " ";
        }
        verbose_stream() << "\n";
#endif
        delete_table();
    }

    void reset() {
        if (m_size == 0) 
            return;
        finalize();
    }

    void finalize() {
        delete_table();
        init(m_init_slots, m_init_cellar);
    }

    bool empty() const {
        return m_size == 0;
    }

    unsigned size() const {
        return m_size;
    }

    unsigned capacity() const {
        return m_capacity;
    }

    unsigned used_slots() const {
        return m_used_slots;
    }

    void insert_fresh(T const& d) {
        if (!has_free_cells()) {
            expand_table();
        }
        unsigned mask = m_slots - 1;
        unsigned h    = get_hash(d);
        unsigned idx  = h & mask;
        cell * c      = m_table + idx;
        cell * new_c  = nullptr;
        m_size++;
        if (c->is_free()) {
            m_used_slots++;
        }
        else {
            new_c = get_free_cell();
            *new_c = *c;
        }
        c->m_next = new_c;
        c->m_data = d;
        CASSERT("chashtable_bug", check_invariant());
    }
    
    void insert(T const & d) {
        if (!has_free_cells())
            expand_table();
        unsigned mask = m_slots - 1;
        unsigned h    = get_hash(d);
        unsigned idx  = h & mask;
        cell * c      = m_table + idx;
        if (c->is_free()) {
            m_size++;
            m_used_slots++;
            c->m_data = d;
            c->m_next = nullptr;
            CASSERT("chashtable_bug", check_invariant());
            return;
        }
        else {
            cell * it = c;
            do { 
                if (equals(it->m_data, d)) {
                    // already there
                    it->m_data = d;
                    CASSERT("chashtable_bug", check_invariant());
                    return;
                }
                CHS_CODE(m_collisions++;);
                it = it->m_next;
            }
            while (it != nullptr);
            // d is not in the table.
            m_size++;
            cell * new_c = get_free_cell();
            *new_c = *c;
            c->m_data    = d;
            c->m_next    = new_c;
            CASSERT("chashtable_bug", check_invariant());
            return;
        }
    }

    T & insert_if_not_there(T const & d) {
        if (!has_free_cells())
            expand_table();
        unsigned mask = m_slots - 1;
        unsigned h    = get_hash(d);
        unsigned idx  = h & mask;
        cell * c      = m_table + idx;
        if (c->is_free()) {
            m_size++;
            m_used_slots++;
            c->m_data = d;
            c->m_next = nullptr;
            CASSERT("chashtable_bug", check_invariant());
            return c->m_data;
        }
        else {
            cell * it = c;
            do { 
                if (equals(it->m_data, d)) {
                    // already there
                    CASSERT("chashtable_bug", check_invariant());
                    return it->m_data;
                }
                CHS_CODE(m_collisions++;);
                it = it->m_next;
            }
            while (it != nullptr);
            // d is not in the table.
            m_size++;
            cell * new_c = get_free_cell();
            *new_c = *c;
            c->m_data    = d;
            c->m_next    = new_c;
            CASSERT("chashtable_bug", check_invariant());
            return c->m_data;
        }
    }

    bool insert_if_not_there2(T const & d) {
        if (!has_free_cells())
            expand_table();
        unsigned mask = m_slots - 1;
        unsigned h    = get_hash(d);
        unsigned idx  = h & mask;
        cell * c      = m_table + idx;
        if (c->is_free()) {
            m_size++;
            m_used_slots++;
            c->m_data = d;
            c->m_next = nullptr;
            CASSERT("chashtable_bug", check_invariant());
            return true;
        }
        else {
            cell * it = c;
            do { 
                if (equals(it->m_data, d)) {
                    // already there
                    CASSERT("chashtable_bug", check_invariant());
                    return false;
                }
                CHS_CODE(m_collisions++;);
                it = it->m_next;
            }
            while (it != nullptr);
            // d is not in the table.
            m_size++;
            cell * new_c = get_free_cell();
            *new_c = *c;
            c->m_data    = d;
            c->m_next    = new_c;
            CASSERT("chashtable_bug", check_invariant());
            return true;
        }
    }

    bool contains(T const & d) const {
        unsigned mask = m_slots - 1;
        unsigned h    = get_hash(d);
        unsigned idx  = h & mask;
        cell * c      = m_table + idx;
        if (c->is_free())
            return false;
        do { 
            if (equals(c->m_data, d)) {
                return true;
            }
            CHS_CODE(const_cast<chashtable*>(this)->m_collisions++;);
            c = c->m_next;
        }
        while (c != nullptr);
        return false;
    }

    T * find_core(T const & d) const {
        unsigned mask = m_slots - 1;
        unsigned h    = get_hash(d);
        unsigned idx  = h & mask;
        cell * c      = m_table + idx;
        if (c->is_free())
            return nullptr;
        do { 
            if (equals(c->m_data, d)) {
                return &(c->m_data);
            }
            CHS_CODE(const_cast<chashtable*>(this)->m_collisions++;);
            c = c->m_next;
        }
        while (c != nullptr);
        return nullptr;
    }

    bool find(T const & d, T & r) {
        unsigned mask = m_slots - 1;
        unsigned h    = get_hash(d);
        unsigned idx  = h & mask;
        cell * c      = m_table + idx;
        if (c->is_free())
            return false;
        do { 
            if (equals(c->m_data, d)) {
                r = c->m_data;
                return true;
            }
            CHS_CODE(const_cast<chashtable*>(this)->m_collisions++;);
            c = c->m_next;
        }
        while (c != nullptr);
        return false;
    }

    void erase(T const & d) {
        unsigned mask = m_slots - 1;
        unsigned h    = get_hash(d);
        unsigned idx  = h & mask;
        cell * c      = m_table + idx;
        if (c->is_free())
            return; 
        cell * prev = nullptr;
        do { 
            if (equals(c->m_data, d)) {
                m_size--;
                if (prev == nullptr) {
                    cell * next = c->m_next;
                    if (next == nullptr) {
                        m_used_slots--;
                        c->mark_free();
                        SASSERT(c->is_free());
                    }
                    else {
                        *c = *next;
                        recycle_cell(next);
                    }
                }
                else {
                    prev->m_next = c->m_next;
                    recycle_cell(c);
                }
                CASSERT("chashtable_bug", check_invariant());
                return;
            }
            CHS_CODE(m_collisions++;);
            prev = c;
            c = c->m_next;
        }
        while (c != nullptr);
    }

    class iterator {
        cell  * m_it;
        cell  * m_end;
        cell  * m_list_it;

        void move_to_used() {
            while (m_it != m_end) {
                if (!m_it->is_free()) {
                    m_list_it = m_it;
                    return;
                }
                m_it++;
            }
            m_list_it = nullptr;
        }
        
    public:
        iterator(cell * start, cell * end): m_it(start), m_end(end) { move_to_used(); }
        iterator():m_it(nullptr), m_end(nullptr), m_list_it(nullptr) {}
        T & operator*() { 
            return m_list_it->m_data; 
        }
        T const & operator*() const { 
            return m_list_it->m_data; 
        }
        T const * operator->() const { return &(operator*()); }
        T * operator->() { return &(operator*()); }
        iterator & operator++() { 
            m_list_it = m_list_it->m_next;
            if (m_list_it == nullptr) {
                m_it++;
                move_to_used();
            }
            return *this;
        }
        iterator operator++(int) { iterator tmp = *this; ++*this; return tmp; }
        bool operator==(iterator const & it) const { return m_list_it == it.m_list_it; }
        bool operator!=(iterator const & it) const { return m_list_it != it.m_list_it; }
    };
    
    iterator begin() const { return iterator(m_table, m_table + m_slots); }
    iterator end() const { return iterator(); }

    void swap(chashtable & other) {
        std::swap(m_table,       other.m_table);
        std::swap(m_capacity,    other.m_capacity);
        std::swap(m_init_slots,  other.m_init_slots);
        std::swap(m_init_cellar, other.m_init_cellar);
        std::swap(m_slots,       other.m_slots);
        std::swap(m_used_slots,  other.m_used_slots);
        std::swap(m_size,        other.m_size);
#ifdef CH_STATISTICS
        std::swap(m_collisions,  other.m_collisions);
#endif
        std::swap(m_next_cell,   other.m_next_cell);
        std::swap(m_free_cell,   other.m_free_cell);
    }

    unsigned collisions() const {
#ifdef CH_STATISTICS
        return m_collisions;
#else
        return 0;
#endif
    }

#ifdef Z3DEBUG
    bool check_invariant() const {
        ptr_addr_hashtable<cell> visited;
        unsigned sz = 0;
        cell *  _end = m_table + m_slots;
        for (cell * it = m_table; it != _end; ++it) {
            if (!it->is_free()) {
                cell * list_it = it;
                while (list_it != 0) {
                    sz++;
                    SASSERT(!visited.contains(list_it));
                    visited.insert(list_it);
                    list_it = list_it->m_next;
                }
            }
        }
        SASSERT(m_size == sz);
        return true;
    }
#endif
};

template<typename Key, typename Value, typename HashProc, typename EqProc>
class cmap {
public:
    struct key_value {
        Key    m_key;
        Value  m_value;
        key_value() {}
        key_value(Key const & k):m_key(k) {}
        key_value(Key const & k, Value const & v):m_key(k), m_value(v) {}
    };

protected:
    struct key_value_hash_proc : private HashProc {
        key_value_hash_proc(HashProc const & p):HashProc(p) {}
        unsigned operator()(key_value const & d) const { return HashProc::operator()(d.m_key); }
    };

    struct key_value_eq_proc : private EqProc {
        key_value_eq_proc(EqProc const & p):EqProc(p) {}
        bool operator()(key_value const & d1, key_value const & d2) const { return EqProc::operator()(d1.m_key, d2.m_key); }
    };

    typedef chashtable<key_value, key_value_hash_proc, key_value_eq_proc> table;
    
    table m_table;

public:
    cmap(HashProc const & h = HashProc(),
         EqProc const & e = EqProc(),
         unsigned init_slots  = table::default_init_slots,
         unsigned init_cellar = table::default_init_cellar):
        m_table(key_value_hash_proc(h),
                key_value_eq_proc(e),
                init_slots,
                init_cellar) {
    }

    typedef typename table::iterator iterator;
    
    void reset() {
        m_table.reset();
    }

    void finalize() {
        m_table.finalize();
    }
    
    bool empty() const { 
        return m_table.empty();
    }
    
    unsigned size() const { 
        return m_table.size(); 
    }
    
    unsigned capacity() const { 
        return m_table.capacity();
    }

    unsigned used_slots() const { 
        return m_table.used_slots();
    }

    unsigned collisions() const {
        return m_table.collisions();
    }
    
    iterator begin() const { 
        return m_table.begin();
    }
    
    iterator end() const { 
        return m_table.end();
    }
    
    void insert(Key const & k, Value const & v) {
        return m_table.insert(key_value(k, v));
    }

    key_value & insert_if_not_there(Key const & k, Value const & v) {
        return m_table.insert_if_not_there(key_value(k, v));
    }

    bool contains(Key const & k) const {
        return m_table.contains(key_value(k));
    }

    key_value * find_core(Key const & k) const {
        return m_table.find_core(key_value(k)); 
    }

    bool find(Key const & k, Value & v) const {
        key_value * e = m_table.find_core(key_value(k));
        if (e == nullptr)
            return false;
        v = e->m_value;
        return true;
    }

    void erase(Key const & k) {
        m_table.erase(key_value(k));
    }
};

#endif
