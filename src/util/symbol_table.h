/*++
Copyright (c) 2006 Microsoft Corporation

Module Name:

    symbol_table.h

Abstract:

    Symbol table for parsing.

Author:

    Leonardo de Moura (leonardo) 2006-09-19.

Revision History:

--*/
#pragma once
#include "util/vector.h"
#include "util/hashtable.h"
#include "util/hash.h"
#include "util/symbol.h"

/**
   \brief Quick & Dirty symbol table.
*/
template<typename T>
class symbol_table {
    struct key_data {
        symbol   m_key;
        T        m_data;
     
        key_data() {
        }

        explicit key_data(symbol k):
            m_key(k) {
        }
        
        key_data(symbol k, const T & d):
            m_key(k), 
            m_data(d) {
        }
    };

    struct key_data_hash_proc { 
        unsigned operator()(const key_data & k) const { 
            return k.m_key.hash();
        } 
    };

    struct key_data_eq_proc { 
        bool operator()(const key_data & k1, const key_data & k2) const { 
            return k1.m_key == k2.m_key;
        } 
    };

    struct hash_entry {
        typedef key_data data;
        key_data m_data;
     
        hash_entry() {
            SASSERT(m_data.m_key == symbol::null);
        }

        unsigned get_hash() const { 
            return m_data.m_key.hash();
        }

        bool is_free() const { 
            return m_data.m_key == symbol::null;
        }

        bool is_deleted() const { 
            return m_data.m_key == symbol::dummy();
        }

        bool is_used() const { 
            return !is_free() && !is_deleted(); 
        }

        key_data & get_data() { 
            return m_data; 
        }

        const key_data & get_data() const { 
            return m_data; 
        }

        void set_data(const key_data & d) { 
            m_data = d; 
        }

        static void set_hash(unsigned h) { 
        }

        void mark_as_deleted() { 
            m_data.m_key = symbol::dummy();
        }
        
        void mark_as_free() { 
            m_data.m_key = symbol::null;
        }
    };
  
    typedef core_hashtable<hash_entry, key_data_hash_proc, key_data_eq_proc> sym_table;
    typedef vector<key_data> trail_stack;
    sym_table   m_sym_table;
    trail_stack m_trail_stack;
    int_vector  m_trail_lims;

public:
    void reset() {
        m_sym_table.reset();
        m_trail_stack.reset();
        m_trail_lims.reset();
    }

    bool find(symbol key, T & result) const {
        key_data dummy(key);
        hash_entry * e = m_sym_table.find_core(dummy);
        if (e == nullptr) {
            return false;
        }
        result = e->get_data().m_data;
        return true;
    }
    
    bool contains(symbol key) const { 
        return m_sym_table.contains(key_data(key)); 
    }

    unsigned get_scope_level() const { 
        return m_trail_lims.size(); 
    }
    
    void insert(symbol key, const T & data) {
        if (get_scope_level() > 0) {
            key_data dummy(key);
            hash_entry * e = m_sym_table.find_core(dummy);
            if (e != nullptr) {
                m_trail_stack.push_back(e->m_data);
                e->m_data.m_data = data;
            }
            else {
                m_trail_stack.push_back(dummy);
                key_data & new_entry = m_trail_stack.back();
                new_entry.m_key = symbol::mark(new_entry.m_key);
                m_sym_table.insert(key_data(key, data));
            }
        }
        else {
            m_sym_table.insert(key_data(key, data));
        }
    }
    
    void begin_scope() { 
        m_trail_lims.push_back(m_trail_stack.size()); 
    }
    
    void end_scope() {
        unsigned old_size = m_trail_lims.back();
        m_trail_lims.pop_back();
        unsigned curr_size = m_trail_stack.size();
        SASSERT(old_size <= curr_size);
        for (unsigned i = old_size; i < curr_size; i++) {
            key_data & curr_entry = m_trail_stack.back();
            symbol key = curr_entry.m_key;
            if (key.is_marked()) {
                curr_entry.m_key = symbol::unmark(key);
                m_sym_table.erase(curr_entry);
            }
            else {
                m_sym_table.insert(curr_entry);
            }
            m_trail_stack.pop_back();
        }
        SASSERT(m_trail_stack.size() == old_size);
    }

    void append(symbol_table<T> const& other) { 
        for (auto const& kv : other.m_sym_table) {
            insert(kv.m_key, kv.m_data);                
        }
    }

    void get_range(vector<T,false>& range) const {
        for (auto kv : m_sym_table) {
            range.push_back(kv.m_data);
        }
    }

    void get_dom(svector<symbol>& dom) const {
        for (auto kv : m_sym_table) {
            dom.push_back(kv.m_key);
        }
    }
};


