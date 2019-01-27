/*++
Copyright (c) 2006 Microsoft Corporation

Module Name:

    obj_triple_hashtable.h

Abstract:

    <abstract>

Author:

    Leonardo de Moura (leonardo) 2008-02-19.

Revision History:

--*/
#ifndef OBJ_TRIPLE_HASHTABLE_H_
#define OBJ_TRIPLE_HASHTABLE_H_

#include "util/hashtable.h"

/**
   \brief Special entry for a hashtable of pairs of obj pointers (i.e.,
   objects that have a hash() method).
   This entry uses 0x0 and 0x1 to represent HT_FREE and HT_DELETED.
*/


template<typename T1, typename T2, typename T3>
class obj_triple_hash_entry {
    unsigned            m_hash; // cached hash code
    triple<T1*, T2*, T3*> m_data;
    
public:
    typedef triple<T1*, T2*, T3*> data;
    obj_triple_hash_entry():m_data(0,0,0) {}
    unsigned get_hash() const { return m_hash; }
    bool is_free() const { return m_data.first == 0; }
    bool is_deleted() const { return m_data.first == reinterpret_cast<T1 *>(1); }
    bool is_used() const { return m_data.first != reinterpret_cast<T1 *>(0) && m_data.first != reinterpret_cast<T1 *>(1); }
    data const & get_data() const { return m_data; }
    data & get_data() { return m_data; }
    void set_data(data const d) { m_data = d; }
    void set_hash(unsigned h) { m_hash = h; }
    void mark_as_deleted() { m_data.first = reinterpret_cast<T1 *>(1); }
    void mark_as_free() { m_data.first = 0; }
};

template<typename T1, typename T2, typename T3>
    class obj_triple_hashtable : public core_hashtable<obj_triple_hash_entry<T1, T2, T3>, obj_ptr_triple_hash<T1, T2, T3>, default_eq<triple<T1*, T2*, T3*> > > {
public:
    obj_triple_hashtable(unsigned initial_capacity = DEFAULT_HASHTABLE_INITIAL_CAPACITY):
        core_hashtable<obj_triple_hash_entry<T1, T2, T3>, obj_ptr_triple_hash<T1, T2, T3>, default_eq<triple<T1*, T2*, T3*> > >(initial_capacity) {
    }
};

template<typename Key1, typename Key2, typename Key3, typename Value>
class obj_triple_map {
protected:
    class entry;
public:
    class key_data {
        Key1 *   m_key1;
        Key2 *   m_key2;
        Key3 *   m_key3;
        Value    m_value;
        unsigned m_hash;
        friend class entry;
    public:
        key_data():
            m_key1(nullptr),
            m_key2(nullptr),
            m_key3(nullptr),
            m_hash(0) {
        }
        key_data(Key1 * k1, Key2 * k2, Key3 * k3):
            m_key1(k1), 
            m_key2(k2),
            m_key3(k3){
            m_hash = combine_hash(combine_hash(m_key1->hash(), m_key2->hash()), m_key3->hash());
        }
        key_data(Key1 * k1, Key2 * k2, Key3* k3, const Value & v):
            m_key1(k1),
            m_key2(k2),
            m_key3(k3),
            m_value(v) {
            m_hash = combine_hash(combine_hash(m_key1->hash(), m_key2->hash()), m_key3->hash());
        }
        unsigned hash() const { return m_hash; }
        bool operator==(key_data const & other) const { return m_key1 == other.m_key1 && m_key2 == other.m_key2 && m_key3 == other.m_key3; }
        Key1 * get_key1() const { return m_key1; }
        Key2 * get_key2() const { return m_key2; }
        Key3 * get_key3() const { return m_key3; }
        Value const & get_value() const { return m_value; }
    };
protected:
    class entry {
        key_data m_data;
    public:
        typedef key_data data;
        entry() {}
        unsigned get_hash() const { return m_data.hash(); }
        bool is_free() const { return m_data.m_key1 == nullptr; }
        bool is_deleted() const { return m_data.m_key1 == reinterpret_cast<Key1 *>(1); }
        bool is_used() const { return m_data.m_key1 != reinterpret_cast<Key1 *>(0) && m_data.m_key1 != reinterpret_cast<Key1 *>(1); }
        key_data const & get_data() const { return m_data; }
        key_data & get_data() { return m_data; }
        void set_data(key_data const & d) { m_data = d; }
        void set_hash(unsigned h) { SASSERT(h == m_data.hash()); }
        void mark_as_deleted() { m_data.m_key1 = reinterpret_cast<Key1 *>(1); }
        void mark_as_free() { m_data.m_key1 = nullptr; }
    };

    typedef core_hashtable<entry, obj_hash<key_data>, default_eq<key_data> > table;

    table m_table;
  
    entry * find_core(Key1 * k1, Key2 * k2, Key3 * k3) const {
        return m_table.find_core(key_data(k1, k2, k3));
    }

public:
    obj_triple_map():
        m_table(DEFAULT_HASHTABLE_INITIAL_CAPACITY) {}
    
    typedef typename table::iterator iterator;
    
    void reset() {
        m_table.reset();
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
    
    iterator begin() const { 
        return m_table.begin();
    }
    
    iterator end() const { 
        return m_table.end();
    }
    
    void insert(Key1 * k1, Key2 * k2, Key3* k3, Value const & v) {
        m_table.insert(key_data(k1, k2, k3, v));
    }
    
    key_data const & insert_if_not_there(Key1 * k1, Key2 * k2, Key3 * k3, Value const & v) {
        return m_table.insert_if_not_there(key_data(k1, k2, k3, v));
    }
    
    bool find(Key1 * k1, Key2 * k2,Key3 * k3, Value & v) const {
        entry * e = find_core(k1, k2, k3);
        if (e) {
            v = e->get_data().get_value();
        }
        return (nullptr != e);
    }
  
    bool contains(Key1 * k1, Key2 * k2, Key3 * k3) const { 
        return find_core(k1, k2, k3) != 0; 
    }
    
    void erase(Key1 * k1, Key2 * k2, Key3 * k3) {
        m_table.remove(key_data(k1, k2, k3));
    }
};

#endif /* OBJ_TRIPLE_HASHTABLE_H_ */

