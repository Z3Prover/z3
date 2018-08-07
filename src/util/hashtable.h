/*++
Copyright (c) 2006 Microsoft Corporation

Module Name:

    hashtable.h

Abstract:

    Hashtable without buckets.

Author:

    Leonardo de Moura (leonardo) 2006-09-11.

Revision History:

--*/
#ifndef HASHTABLE_H_
#define HASHTABLE_H_
#include "util/debug.h"
#include <ostream>
#include "util/util.h"
#include <climits>
#include "util/memory_manager.h"
#include "util/hash.h"
#include "util/vector.h"

#define DEFAULT_HASHTABLE_INITIAL_CAPACITY 8
#define SMALL_TABLE_CAPACITY               64

//  #define HASHTABLE_STATISTICS

#ifdef HASHTABLE_STATISTICS
#define HS_CODE(CODE) { CODE }
#else
#define HS_CODE(CODE) 
#endif

typedef enum { HT_FREE, 
               HT_DELETED,
               HT_USED } hash_entry_state;

template<typename T>
class default_hash_entry {
    unsigned         m_hash; //!< cached hash code
    hash_entry_state m_state;
    T                m_data;
public:
    typedef T         data;
    default_hash_entry():m_state(HT_FREE) {}
    unsigned get_hash() const  { return m_hash; }
    bool is_free() const { return m_state == HT_FREE; }
    bool is_deleted() const { return m_state == HT_DELETED; }
    bool is_used() const { return m_state == HT_USED; }
    T & get_data()             { return m_data; }
    const T & get_data() const { return m_data; }
    void set_data(T && d) { m_data = std::move(d); m_state = HT_USED; }
    void set_hash(unsigned h)  { m_hash = h; }
    void mark_as_deleted() { m_state = HT_DELETED; }
    void mark_as_free() { m_state = HT_FREE; }
};

/**
   \brief Special entry for a hashtable of integers. This entry "steals" two values for representing HT_FREE and HT_DELETED.
*/
template<int Free, int Deleted>
class int_hash_entry {
    unsigned         m_hash; //!< cached hash code
    int              m_data;
public:
    typedef int data;
    int_hash_entry():m_data(Free) {}
    unsigned get_hash() const { return m_hash; }
    bool is_free() const { return m_data == Free; }
    bool is_deleted() const { return m_data == Deleted; }
    bool is_used() const { return m_data != Free && m_data != Deleted; }
    int get_data() const { return m_data; }
    int & get_data() { return m_data; }
    void set_data(int d) { m_data = d; }
    void set_hash(unsigned h) { m_hash = h; }
    void mark_as_deleted() { m_data = Deleted; }
    void mark_as_free() { m_data = Free; }
};

/**
   \brief Special entry for a hashtable of pointers. This entry uses 0x0 and 0x1 to represent HT_FREE and HT_DELETED.
*/
template<typename T>
class ptr_hash_entry {
    unsigned        m_hash; //!< cached hash code
    T *             m_ptr;
public:
    typedef T * data;
    ptr_hash_entry():m_ptr(nullptr) {}
    unsigned get_hash() const { return m_hash; }
    bool is_free() const { return m_ptr == nullptr; }
    bool is_deleted() const { return m_ptr == reinterpret_cast<T *>(1); }
    bool is_used() const { return m_ptr != reinterpret_cast<T *>(0) && m_ptr != reinterpret_cast<T *>(1); }
    T * get_data() const { return m_ptr; }
    T * & get_data() { return m_ptr; }
    void set_data(T * d) { m_ptr = d; }
    void set_hash(unsigned h) { m_hash = h; }
    void mark_as_deleted() { m_ptr = reinterpret_cast<T *>(1); }
    void mark_as_free() { m_ptr = nullptr; }
};


/**
   \brief Special entry for a hashtable of pointers which uses the pointer itself as the hashcode. 
   This entry uses 0x0 and 0x1 to represent HT_FREE and HT_DELETED.
*/
template<typename T>
class ptr_addr_hash_entry : public ptr_hash_entry<T> {
    T *             m_ptr;
public:
    typedef T * data;
    ptr_addr_hash_entry():m_ptr(nullptr) {}
    unsigned get_hash() const { return get_ptr_hash(m_ptr); }
    bool is_free() const { return m_ptr == nullptr; }
    bool is_deleted() const { return m_ptr == reinterpret_cast<T *>(1); }
    bool is_used() const { return m_ptr != reinterpret_cast<T *>(0) && m_ptr != reinterpret_cast<T *>(1); }
    T * get_data() const { return m_ptr; }
    T * & get_data() { return m_ptr; }
    void set_data(T * d) { m_ptr = d; }
    void set_hash(unsigned h) { SASSERT(h == get_ptr_hash(m_ptr)); /* do nothing */ }
    void mark_as_deleted() { m_ptr = reinterpret_cast<T *>(1); }
    void mark_as_free() { m_ptr = 0; }
};

template<typename Entry, typename HashProc, typename EqProc>
class core_hashtable : private HashProc, private EqProc {
protected:
    Entry *  m_table;
    unsigned m_capacity;
    unsigned m_size;
    unsigned m_num_deleted;
#ifdef HASHTABLE_STATISTICS
    unsigned long long m_st_collision;
#endif

    Entry* alloc_table(unsigned size) {
        Entry* entries = alloc_vect<Entry>(size); 
        return entries;
    }

    void delete_table() {
        dealloc_vect(m_table, m_capacity);
        m_table = nullptr;
    }

public:
    typedef typename Entry::data data;
    typedef Entry                entry;
protected:
    unsigned get_hash(data const & e) const { return HashProc::operator()(e); }
    bool equals(data const & e1, data const & e2) const { return EqProc::operator()(e1, e2); }
    
    static void copy_table(entry * source, unsigned source_capacity, entry * target, unsigned target_capacity) {
        SASSERT(target_capacity >= source_capacity);
        unsigned target_mask = target_capacity - 1;
        entry *  source_end  = source + source_capacity;
        entry *  target_end  = target + target_capacity;
        for (entry * source_curr = source; source_curr != source_end; ++source_curr) {
            if (source_curr->is_used()) {
                unsigned hash = source_curr->get_hash();
                unsigned idx  = hash & target_mask;
                entry * target_begin = target + idx;
                entry * target_curr  = target_begin;
                for (; target_curr != target_end; ++target_curr) {
                    SASSERT(!target_curr->is_deleted());
                    if (target_curr->is_free()) {
                        *target_curr = *source_curr;
                        goto end;
                    }
                }
                for (target_curr = target; target_curr != target_begin; ++target_curr) {
                    SASSERT(!target_curr->is_deleted());
                    if (target_curr->is_free()) {
                        *target_curr = *source_curr;
                        goto end;
                    }
                }
                UNREACHABLE();
            end:
                ;
            }
        } 
    }

    static void move_table(entry * source, unsigned source_capacity, entry * target, unsigned target_capacity) {
        SASSERT(target_capacity >= source_capacity);
        unsigned target_mask = target_capacity - 1;
        entry *  source_end = source + source_capacity;
        entry *  target_end = target + target_capacity;
        for (entry * source_curr = source; source_curr != source_end; ++source_curr) {
            if (source_curr->is_used()) {
                unsigned hash = source_curr->get_hash();
                unsigned idx = hash & target_mask;
                entry * target_begin = target + idx;
                entry * target_curr = target_begin;
                for (; target_curr != target_end; ++target_curr) {
                    SASSERT(!target_curr->is_deleted());
                    if (target_curr->is_free()) {
                        *target_curr = std::move(*source_curr);
                        goto end;
                    }
                }
                for (target_curr = target; target_curr != target_begin; ++target_curr) {
                    SASSERT(!target_curr->is_deleted());
                    if (target_curr->is_free()) {
                        *target_curr = std::move(*source_curr);
                        goto end;
                    }
                }
                UNREACHABLE();
            end:
                ;
            }
        }
    }

    void expand_table() {
        unsigned new_capacity = m_capacity << 1;
        entry *  new_table    = alloc_table(new_capacity);
        move_table(m_table, m_capacity, new_table, new_capacity);
        delete_table();
        m_table       = new_table;
        m_capacity    = new_capacity;
        m_num_deleted = 0;
    }

    
    void remove_deleted_entries() {
        if (memory::is_out_of_memory())
            return;
        entry * new_table = alloc_table(m_capacity);
        move_table(m_table, m_capacity, new_table, m_capacity);
        delete_table();
        m_table       = new_table;
        m_num_deleted = 0;
    }
    
public:
    core_hashtable(unsigned initial_capacity = DEFAULT_HASHTABLE_INITIAL_CAPACITY, 
                   HashProc const & h = HashProc(), 
                   EqProc const & e = EqProc()):
        HashProc(h),
        EqProc(e) {
        SASSERT(is_power_of_two(initial_capacity));
        m_table       = alloc_table(initial_capacity);
        m_capacity    = initial_capacity;
        m_size        = 0;
        m_num_deleted = 0;
        HS_CODE({
            m_st_collision = 0;
        });
    }

    core_hashtable(const core_hashtable & source):
        HashProc(source),
        EqProc(source) {
        m_capacity    = source.m_capacity;
        m_table       = alloc_table(m_capacity);
        copy_table(source.m_table, m_capacity, m_table, m_capacity);
        m_size        = source.m_size;
        m_num_deleted = 0;
        HS_CODE({
            m_st_collision = 0;
        });
    }
    
    ~core_hashtable() {
        delete_table();
    }

    void swap(core_hashtable & source) {
        std::swap(m_table,       source.m_table);
        std::swap(m_capacity,    source.m_capacity);
        std::swap(m_size,        source.m_size);
        std::swap(m_num_deleted, source.m_num_deleted);
        HS_CODE({
            std::swap(m_st_collision, source.m_st_collision);
        });
    }

    void reset() {
        if (m_size == 0 && m_num_deleted == 0)
            return;
        unsigned overhead = 0;
        entry * curr      = m_table;
        entry * end       = m_table + m_capacity;
        for (; curr != end; ++curr) {
            if (!curr->is_free())
                curr->mark_as_free();
            else
                overhead++;
        }
        if (m_capacity > 16 && overhead << 2 > (m_capacity * 3)) {
            delete_table();
            SASSERT(m_capacity > 16);
            SASSERT(is_power_of_two(m_capacity));
            m_capacity = (m_capacity >> 1);
            SASSERT(is_power_of_two(m_capacity));
            m_table    = alloc_table(m_capacity);
        }
        m_size        = 0;
        m_num_deleted = 0;
    }

    void finalize() {
        if (m_capacity > SMALL_TABLE_CAPACITY) {
            delete_table();
            m_table       = alloc_table(SMALL_TABLE_CAPACITY);
            m_capacity    = SMALL_TABLE_CAPACITY;
            m_size        = 0;
            m_num_deleted = 0;
        }
        else {
            reset();
        }
    }
    
    class iterator {
        entry * m_curr;
        entry * m_end;
        void move_to_used() {
            while (m_curr != m_end && !m_curr->is_used()) {
                m_curr++;
            }
        }
    public:
        iterator(entry * start, entry * end): m_curr(start), m_end(end) { move_to_used(); }
        data & operator*() { return m_curr->get_data(); }
        data const & operator*() const { return m_curr->get_data(); }
        data const * operator->() const { return &(operator*()); }
        data * operator->() { return &(operator*()); }
        iterator & operator++() { ++m_curr; move_to_used(); return *this; }
        iterator operator++(int) { iterator tmp = *this; ++*this; return tmp; }
        bool operator==(iterator const & it) const { return m_curr == it.m_curr; }
        bool operator!=(iterator const & it) const { return m_curr != it.m_curr; }
    };
    
    bool empty() const { return m_size == 0; }
    
    unsigned size() const { return m_size; }
    
    unsigned capacity() const { return m_capacity; }
    
    iterator begin() const { return iterator(m_table, m_table + m_capacity); }
    
    iterator end() const { return iterator(m_table + m_capacity, m_table + m_capacity); }
    
#define INSERT_LOOP_BODY() {                                                            \
        if (curr->is_used()) {                                                          \
            if (curr->get_hash() == hash && equals(curr->get_data(), e)) {              \
                curr->set_data(std::move(e));                                           \
                return;                                                                 \
            }                                                                           \
            HS_CODE(m_st_collision++;);                                                 \
        }                                                                               \
        else if (curr->is_free()) {                                                     \
            entry * new_entry;                                                          \
            if (del_entry) { new_entry = del_entry; m_num_deleted--; }                  \
            else { new_entry = curr; }                                                  \
            new_entry->set_data(std::move(e));                                          \
            new_entry->set_hash(hash);                                                  \
            m_size++;                                                                   \
            return;                                                                     \
        }                                                                               \
        else {                                                                          \
            SASSERT(curr->is_deleted());                                                \
            del_entry = curr;                                                           \
            HS_CODE(m_st_collision++;);                                                 \
        }                                                                               \
    } ((void) 0)

    void insert(data && e) {
        if (((m_size + m_num_deleted) << 2) > (m_capacity * 3)) {
            expand_table();
        }
        unsigned hash     = get_hash(e);
        unsigned mask     = m_capacity - 1;
        unsigned idx      = hash & mask;
        entry * begin     = m_table + idx;
        entry * end       = m_table + m_capacity;
        entry * curr      = begin;
        entry * del_entry = nullptr;
        for (; curr != end; ++curr) {
            INSERT_LOOP_BODY();
        }
        for (curr = m_table; curr != begin; ++curr) {
            INSERT_LOOP_BODY();
        }
        UNREACHABLE();
    }

    void insert(const data & e) {
        data tmp(e);
        insert(std::move(tmp));
    }

#define INSERT_LOOP_CORE_BODY() {                                               \
        if (curr->is_used()) {                                                  \
            if (curr->get_hash() == hash && equals(curr->get_data(), e)) {      \
                et = curr;                                                      \
                return false;                                                   \
            }                                                                   \
            HS_CODE(m_st_collision++;);                                         \
        }                                                                       \
        else if (curr->is_free()) {                                             \
            entry * new_entry;                                                  \
            if (del_entry) { new_entry = del_entry; m_num_deleted--; }          \
            else { new_entry = curr; }                                          \
            new_entry->set_data(std::move(e));                                  \
            new_entry->set_hash(hash);                                          \
            m_size++;                                                           \
            et = new_entry;                                                     \
            return true;                                                        \
        }                                                                       \
        else {                                                                  \
            SASSERT(curr->is_deleted());                                        \
            del_entry = curr;                                                   \
            HS_CODE(m_st_collision++;);                                         \
        }                                                                       \
    } ((void) 0)

    /**
       \brief Insert the element e if it is not in the table.
       Return true if it is a new element, and false otherwise.
       Store the entry/slot of the table in et.
    */
    bool insert_if_not_there_core(data && e, entry * & et) {
        if ((m_size + m_num_deleted) << 2 > (m_capacity * 3)) {
            // if ((m_size + m_num_deleted) * 2 > (m_capacity)) {
            expand_table();
        }
        unsigned hash     = get_hash(e);
        unsigned mask     = m_capacity - 1;
        unsigned idx      = hash & mask;
        entry * begin     = m_table + idx;
        entry * end       = m_table + m_capacity;
        entry * curr      = begin;
        entry * del_entry = nullptr;
        for (; curr != end; ++curr) {
            INSERT_LOOP_CORE_BODY();
        }
        for (curr = m_table; curr != begin; ++curr) {
            INSERT_LOOP_CORE_BODY();
        }
        UNREACHABLE();
        return false;
    }

    bool insert_if_not_there_core(const data & e, entry * & et) {
        data temp(e);
        return insert_if_not_there_core(std::move(temp), et);
    }

    /**
       \brief Insert the element e if it is not in the table.
       Return a reference to e or to an object identical to e
       that was already in the table.
     */
    data const & insert_if_not_there(data const & e) {
        entry * et;
        insert_if_not_there_core(e, et);
        return et->get_data();
    }

    /**
       \brief Insert the element e if it is not in the table.
       Return the entry that contains e.
    */
    entry * insert_if_not_there2(data const & e) {
        entry * et;
        insert_if_not_there_core(e, et);
        return et;
    }
    
#define FIND_LOOP_BODY() {                                                      \
        if (curr->is_used()) {                                                  \
            if (curr->get_hash() == hash && equals(curr->get_data(), e)) {      \
                return curr;                                                    \
            }                                                                   \
            HS_CODE(const_cast<core_hashtable*>(this)->m_st_collision++;);      \
        }                                                                       \
        else if (curr->is_free()) {                                             \
            return 0;                                                           \
        }                                                                       \
        else {                                                                  \
            HS_CODE(const_cast<core_hashtable*>(this)->m_st_collision++;);      \
        }                                                                       \
    } ((void) 0)

    entry * find_core(data const & e) const {
        unsigned hash = get_hash(e);
        unsigned mask = m_capacity - 1;
        unsigned idx  = hash & mask;
        entry * begin = m_table + idx;
        entry * end   = m_table + m_capacity;
        entry * curr  = begin;
        for (; curr != end; ++curr) {
            FIND_LOOP_BODY();
        }
        for (curr = m_table; curr != begin; ++curr) {
            FIND_LOOP_BODY();
        }
        return nullptr;
    }

    bool find(data const & k, data & r) const {
        entry * e = find_core(k);
        if (e != nullptr) {
            r = e->get_data();
            return true;
        }
        return false;
    }
    
    bool contains(data const & e) const { 
        return find_core(e) != nullptr;
    }
    
    iterator find(data const & e) const { 
        entry * r = find_core(e); 
        if (r) {
            return iterator(r, m_table + m_capacity); 
        }
        else {
            return end(); 
        }
    }

#define REMOVE_LOOP_BODY() {                                                    \
        if (curr->is_used()) {                                                  \
            if (curr->get_hash() == hash && equals(curr->get_data(), e)) {      \
                goto end_remove;                                                \
            }                                                                   \
            HS_CODE(m_st_collision++;);                                         \
        }                                                                       \
        else if (curr->is_free()) {                                             \
            return;                                                             \
        }                                                                       \
        HS_CODE(m_st_collision++;);                                             \
    } ((void) 0)

    void remove(data const & e) {
        unsigned hash = get_hash(e);
        unsigned mask = m_capacity - 1;
        unsigned idx  = hash & mask;
        entry * begin = m_table + idx;
        entry * end   = m_table + m_capacity;
        entry * curr  = begin;
        for (; curr != end; ++curr) {
            REMOVE_LOOP_BODY();
        }
        for (curr = m_table; curr != begin; ++curr) {
            REMOVE_LOOP_BODY();
        }
        SASSERT(!contains(e));
        return; // node is not in the table
    end_remove:
        entry * next = curr + 1;                                      
        if (next == end) {
            next = m_table;                          
        }
        if (next->is_free()) {
            curr->mark_as_free();                                       
            m_size--;                                                
        }                                                            
        else {
            curr->mark_as_deleted();                                    
            m_num_deleted++;
            m_size--;
            if (m_num_deleted > m_size && m_num_deleted > SMALL_TABLE_CAPACITY) {
                remove_deleted_entries();
            }
        }
    }

    void erase(data const & e) { remove(e); }
    
    void dump(std::ostream & out) {
        entry * curr = m_table;
        entry * end  = m_table + m_capacity;
        out << "[";
        bool first = true;
        for (; curr != end; ++curr) {
            if (curr->is_used()) {
                if (first) {
                    first = false; 
                }
                else {
                    out << " ";
                }
                out << curr->get_data();
            }
        }
        out << "]";
    }

    core_hashtable& operator|=(core_hashtable const& other) {
        if (this == &other) return *this;
        for (const data& d : other) {
            insert(d);
        }
        return *this;
    }

    core_hashtable& operator&=(core_hashtable const& other) {
        if (this == &other) return *this;
        core_hashtable copy(*this);
        for (const data& d : copy) {
            if (!other.contains(d)) {
                remove(d);
            }
        }
        return *this;
    }

    core_hashtable& operator=(core_hashtable const& other) {
        if (this == &other) return *this;
        reset();
        for (const data& d : other) {
            insert(d);
        }
        return *this;
    }

#ifdef Z3DEBUG
    bool check_invariant() {
        entry * curr = m_table;
        entry * end  = m_table + m_capacity;
        unsigned num_deleted = 0;
        unsigned num_used    = 0;
        for (; curr != end; ++curr) {
            if (curr->is_deleted()) {
                num_deleted ++;
            }
            if (curr->is_used()) {
                num_used++;
            }
        }
        SASSERT(num_deleted == m_num_deleted);
        SASSERT(num_used == m_size);
        return true;
    }
#endif

#ifdef HASHTABLE_STATISTICS
    unsigned long long get_num_collision() const { return m_st_collision; }
#else
    unsigned long long get_num_collision() const { return 0; }
#endif

#define COLL_LOOP_BODY() {                                              \
    if (curr->is_used()) {                                          \
        if (curr->get_hash() == hash && equals(curr->get_data(), e)) return; \
        collisions.push_back(curr->get_data());                         \
        continue;                                                       \
    }                                                                   \
    else if (curr->is_free()) {                                         \
        continue;                                                       \
    }                                                                   \
    collisions.push_back(curr->get_data());                             \
    } ((void) 0);    

    void get_collisions(data const& e, vector<data>& collisions) {        
        unsigned hash = get_hash(e);
        unsigned mask = m_capacity - 1;
        unsigned idx  = hash & mask;
        entry * begin = m_table + idx;
        entry * end   = m_table + m_capacity;
        entry * curr  = begin;
        for (; curr != end; ++curr) {
            COLL_LOOP_BODY();
        }
        for (curr = m_table; curr != begin; ++curr) {
            COLL_LOOP_BODY();
        }

    }
};

template<typename T, typename HashProc, typename EqProc>
class hashtable : public core_hashtable<default_hash_entry<T>, HashProc, EqProc> {
public:
    hashtable(unsigned initial_capacity = DEFAULT_HASHTABLE_INITIAL_CAPACITY, 
              HashProc const & h = HashProc(), 
              EqProc const & e = EqProc()):
        core_hashtable<default_hash_entry<T>, HashProc, EqProc>(initial_capacity, h, e) {}
};

template<typename T, typename HashProc, typename EqProc>
class ptr_hashtable : public core_hashtable<ptr_hash_entry<T>, HashProc, EqProc> {
public:
    ptr_hashtable(unsigned initial_capacity = DEFAULT_HASHTABLE_INITIAL_CAPACITY, 
                  HashProc const & h = HashProc(), 
                  EqProc const & e = EqProc()):
        core_hashtable<ptr_hash_entry<T>, HashProc, EqProc>(initial_capacity, h, e) {}
};

/**
   \brief Hashtable of pointers which use the pointer as the hash-code.
*/
template<typename T>
class ptr_addr_hashtable : public core_hashtable<ptr_addr_hash_entry<T>, ptr_hash<T>, ptr_eq<T> > {
public:
    typedef typename core_hashtable<ptr_addr_hash_entry<T>, ptr_hash<T>, ptr_eq<T> >::iterator iterator;
    ptr_addr_hashtable(unsigned initial_capacity = DEFAULT_HASHTABLE_INITIAL_CAPACITY):
        core_hashtable<ptr_addr_hash_entry<T>, ptr_hash<T>, ptr_eq<T> >(initial_capacity) {}

    iterator begin() const { 
        UNREACHABLE();
    }
    
    iterator end() const { 
        UNREACHABLE();
    }

    // NB. Using iterators to traverse the elements of this kind of hashtable will produce non-determinism.

};

/**
   \brief Simple int_hashtable. The values INT_MIN and INT_MIN + 1 are used to mark
   deleted and free slots. So, these values cannot be stored in the table. Use core_hashtable
   template to avoid this limitation.
 */
template<typename HashProc, typename EqProc>
class int_hashtable : public core_hashtable<int_hash_entry<INT_MIN, INT_MIN + 1>, HashProc, EqProc> {
public:
    int_hashtable(unsigned initial_capacity = DEFAULT_HASHTABLE_INITIAL_CAPACITY, 
                  HashProc const & h = HashProc(), 
                  EqProc const & e = EqProc()):
        core_hashtable<int_hash_entry<INT_MIN, INT_MIN + 1>, HashProc, EqProc>(initial_capacity, h, e) {}
};


#endif /* HASHTABLE_H_ */
