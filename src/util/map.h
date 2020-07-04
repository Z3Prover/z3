/*++
Copyright (c) 2006 Microsoft Corporation

Module Name:

    map.h

Abstract:

    Simple mapping based on the hashtable.

Author:

    Leonardo de Moura (leonardo) 2006-10-14.

Revision History:

--*/
#pragma once

#include "util/hashtable.h"

template<typename Key, typename Value>
struct _key_data {
    Key   m_key;
    Value m_value;
    _key_data() {
    }
    _key_data(Key const & k):
        m_key(k) {
    }
    _key_data(Key const & k, Value const & v):
        m_key(k),
        m_value(v) {
    }
};

template<typename Entry, typename HashProc, typename EqProc>
class table2map {
public:
    typedef Entry    entry;
    typedef typename Entry::key      key;
    typedef typename Entry::value    value;
    typedef typename Entry::key_data key_data;


    struct entry_hash_proc : private HashProc {
        entry_hash_proc(HashProc const & p):
            HashProc(p) {
        }
        
        unsigned operator()(key_data const & d) const { 
            return HashProc::operator()(d.m_key);
        }
    };

    struct entry_eq_proc : private EqProc {
        entry_eq_proc(EqProc const & p):
            EqProc(p) {
        }
    
        bool operator()(key_data const & d1, key_data const & d2) const {
            return EqProc::operator()(d1.m_key, d2.m_key);
        }
    };

    typedef core_hashtable<entry, entry_hash_proc, entry_eq_proc> table;
    
    table m_table;
    
public:
    table2map(HashProc const & h = HashProc(), EqProc const & e = EqProc()):
        m_table(DEFAULT_HASHTABLE_INITIAL_CAPACITY, entry_hash_proc(h), entry_eq_proc(e)) {
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
    
    iterator begin() const { 
        return m_table.begin();
    }
    
    iterator end() const { 
        return m_table.end();
    }
    
    void insert(key const & k, value const & v) {
        m_table.insert(key_data(k, v));
    }
  
    bool insert_if_not_there_core(key const & k, value const & v, entry *& et) {
        return m_table.insert_if_not_there_core(key_data(k,v), et);
    }

    value & insert_if_not_there(key const & k, value const & v) {
        return m_table.insert_if_not_there2(key_data(k, v))->get_data().m_value;
    }
    
    entry * insert_if_not_there3(key const & k, value const & v) {
        return m_table.insert_if_not_there2(key_data(k, v));
    }
        
    entry * find_core(key const & k) const {
        return m_table.find_core(key_data(k));
    }

    bool find(key const & k, value & v) const {
        entry * e = find_core(k);
        if (e) {
            v = e->get_data().m_value;
        }
        return (nullptr != e);
    }

    value const& get(key const& k, value const& default_value) const {
        entry* e = find_core(k);
        if (e) {
            return e->get_data().m_value;
        }
        else {
            return default_value;
        }
    }
        
    iterator find_iterator(key const & k) const { 
        return m_table.find(key_data(k));
    }
    
    value const & find(key const& k) const {
        entry * e = find_core(k);
        SASSERT(e);
        return e->get_data().m_value;
    }

    value & find(key const& k)  {
        entry * e = find_core(k);
        SASSERT(e);
        return e->get_data().m_value;
    }

    value const& operator[](key const& k) const {  return find(k); }

    value& operator[](key const& k) { return find(k); }


    bool contains(key const & k) const { 
        return find_core(k) != nullptr;
    }

    void remove(key const & k) {
        m_table.remove(key_data(k));
    }
    
    void erase(key const & k) {
        remove(k);
    }

    unsigned long long get_num_collision() const { return m_table.get_num_collision(); }

    void swap(table2map & other) {
        m_table.swap(other.m_table);
    }

    bool operator==(table2map const& other) const {
        if (size() != other.size()) return false;
        for (auto const& kv : *this) {
            auto* e = other.find_core(kv.m_key);
            if (!e) return false;
            if (e->get_data().m_value != kv.m_value) return false;
        }
        return true;
    }
    
#ifdef Z3DEBUG
    
    bool check_invariant() { 
        return m_table.check_invariant(); 
    }
    
#endif   
};

template<typename Key, typename Value>
class default_map_entry : public default_hash_entry<_key_data<Key, Value> > {
public:
    typedef Key   key;
    typedef Value value;
    typedef _key_data<Key, Value> key_data;
};


template<typename Key, typename Value, typename HashProc, typename EqProc>
class map : public table2map<default_map_entry<Key, Value>, HashProc, EqProc> {
public:
    map(HashProc const & h = HashProc(), EqProc const & e = EqProc()):
        table2map<default_map_entry<Key, Value>, HashProc, EqProc>(h, e) {
    }
};

template<typename Key, typename Value>
struct _key_ptr_data {
    Key * m_key;
    Value m_value;
    _key_ptr_data():
        m_key(0) {
    }
    _key_ptr_data(Key * k):
        m_key(k) {
    }
    _key_ptr_data(Key * k, Value const & v):
        m_key(k),
        m_value(v) {
    }
};

template<typename Key, typename Value>
class ptr_map_entry {
public:
    typedef _key_ptr_data<Key, Value> key_data;
    typedef _key_ptr_data<Key, Value> data;
private:
    unsigned m_hash; //!< cached hash code
    data     m_data;
public:
    typedef Key * key;
    typedef Value value;
    unsigned get_hash() const { return m_hash; }
    bool is_free() const { return m_data.m_key == 0; }
    bool is_deleted() const { return m_data.m_key == reinterpret_cast<Key *>(1); }
    bool is_used() const { return m_data.m_key != reinterpret_cast<Key *>(0) && m_data.m_key != reinterpret_cast<Key *>(1); }
    key_data const & get_data() const { return m_data; }
    key_data & get_data() { return m_data; }
    void set_data(key_data const & d) { m_data = d; }
    void set_hash(unsigned h) { m_hash = h; }
    void mark_as_deleted() { m_data.m_key = reinterpret_cast<Key *>(1); }
    void mark_as_free() { m_data.m_key = 0; }
};

template<typename Key, typename Value>
class ptr_addr_map_entry {
public:
    typedef _key_ptr_data<Key, Value> key_data;
    typedef _key_ptr_data<Key, Value> data;
private:
    data     m_data;
public:
    typedef Key * key;
    typedef Value value;
    unsigned get_hash() const { return get_ptr_hash(m_data.m_key); }
    bool is_free() const { return m_data.m_key == 0; }
    bool is_deleted() const { return m_data.m_key == reinterpret_cast<Key *>(1); }
    bool is_used() const { return m_data.m_key != reinterpret_cast<Key *>(0) && m_data.m_key != reinterpret_cast<Key *>(1); }
    key_data const & get_data() const { return m_data; }
    key_data & get_data() { return m_data; }
    void set_data(key_data const & d) { m_data = d; }
    void set_hash(unsigned h) { SASSERT(h == get_ptr_hash(m_data.m_key)); /* do nothing */ }
    void mark_as_deleted() { m_data.m_key = reinterpret_cast<Key *>(1); }
    void mark_as_free() { m_data.m_key = 0; }
};

template<typename Key, typename Value>
class ptr_addr_map : public table2map<ptr_addr_map_entry<Key, Value>, ptr_hash<Key>, ptr_eq<Key> > {
public:
};

struct u_hash { unsigned operator()(unsigned u) const { return u; } };

struct u_eq { bool operator()(unsigned u1, unsigned u2) const { return u1 == u2; } };


struct u64_hash { unsigned operator()(uint64_t u) const { return mk_mix((unsigned)u, (unsigned)(u >> 32ull), 0); } };

struct u64_eq { bool operator()(uint64_t u1, uint64_t u2) const { return u1 == u2; } };

struct size_t_eq { bool operator()(size_t u1, size_t u2) const { return u1 == u2; } };

struct int_eq { bool operator()(int u1, int u2) const { return u1 == u2; } };

template<typename Value> 
class u_map : public map<unsigned, Value, u_hash, u_eq> {};

template<typename Value>
class size_t_map : public map<size_t, Value, size_t_hash, size_t_eq> {};

template<typename Value> 
class u64_map : public map<uint64_t, Value, u64_hash, u64_eq> {};

