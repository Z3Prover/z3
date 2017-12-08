/*++
Copyright (c) 2017 Microsoft Corporation

Module Name:

    obj_ref_hashtable.h

Abstract:

    corresponding obj_map with reference count managment.

Author:

    Nikolaj Bjorner (nbjorner) 2017-12-8

Revision History:

--*/
#ifndef OBJ_REF_HASHTABLE_H_
#define OBJ_REF_HASHTABLE_H_

#include "util/obj_hashtable.h"

template<typename M, typename Key, typename Value>
class obj_ref_map {
    M&                  m;
    obj_map<Key, Value> m_table;
public:
    typedef typename obj_map<Key, Value> iterator;
    typedef Key key;
    typedef Value value;
    typedef typename obj_map<Key, Value>::key_data key_data;
    typedef typename obj_map<Key, Value>::obj_map_entry obj_map_entry;

    obj_ref_map(M& m):m(m) {}
    
    ~obj_ref_map() { reset();  }

    void reset() {
        for (auto& kv : m_table) {
            m.dec_ref(kv.m_key);
        }
        m_table.reset();
    }

    void finalize() {
        reset();
        m_table.finalize();
    }

    bool empty() const { return m_table.empty(); }

    unsigned size() const { return m_table.size();  }
    
    unsigned capacity() const { return m_table.capacity();  }
    
    iterator begin() const { return m_table.begin(); }
    
    iterator end() const { return m_table.end();  }
    
    void insert(Key * const k, Value const & v) {
        if (!m_table.contains(k)) m.inc_ref(k);
        m_table.insert(k, v);
    }

    void insert(Key * const k, Value && v) {
        if (!m_table.contains(k)) m.inc_ref(k);
        m_table.insert(k, v);
    }
    
    key_data const & insert_if_not_there(Key * k, Value const & v) {
        if (!m_table.contains(k)) m.inc_ref(k);
        return m_table.insert_if_not_there(k, v);
    }

    obj_map_entry * insert_if_not_there2(Key * k, Value const & v) {
        if (!m_table.contains(k)) m.inc_ref(k);
        return m_table.insert_if_not_there2(k, v);
    }
    
    obj_map_entry * find_core(Key * k) const { return m_table.find_core(k); }

    bool find(Key * const k, Value & v) const { return m_table.find(k, v); }

    value const & find(key * k) const { return m_table.find(k); }

    value & find(key * k)  { return m_table.find(k); }

    value const & operator[](key * k) const { return find(k); }

    value & operator[](key * k) { return find(k); }
    
    iterator find_iterator(Key * k) const { return m_table.find_iterator(k); }

    bool contains(Key * k) const { return m_table.contains(k); }

    void remove(Key * k) { 
        if (m_table.contains(k)) {
            m_table.remove(k);
            m.dec_ref(k);
        }
    }
    
    void erase(Key * k) { remove(k); }

    unsigned long long get_num_collision() const { return m_table.get_num_collision(); }

    void swap(obj_ref_map & other) {
        m_table.swap(other.m_table);
    }

    
};


#endif /* OBJ_REF_HASHTABLE_H_ */

