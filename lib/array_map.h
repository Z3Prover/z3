/*++
Copyright (c) 2006 Microsoft Corporation

Module Name:

    array_map.h

Abstract:

    A mapping for keys that can be mapped to unsigned integers.

Author:

    Leonardo de Moura (leonardo) 2008-01-03.

Revision History:

--*/
#ifndef _ARRAY_MAP_H_
#define _ARRAY_MAP_H_

#include"vector.h"
#include"optional.h"

/**
   \brief Implements a mapping from Key to Data.

   Plugin must provide the following functions:
   - void ins_eh(Key const & k, Data const & d);
   - void del_eh(Key const & k, Data const & d);
   - unsigned to_int(Key const & k);
*/
template<typename Key, typename Data, typename Plugin, bool CallDestructors=true>
class array_map {
    
    struct entry {
        Key      m_key;
        Data     m_data;
        unsigned m_timestamp;
        entry(Key const & k, Data const & d, unsigned t): m_key(k), m_data(d), m_timestamp(t) {}
    };

    unsigned                 m_timestamp;
    unsigned                 m_garbage;
    unsigned                 m_non_garbage;
    static const unsigned    m_gc_threshold = 10000;
    vector<optional<entry>, CallDestructors > m_map;
    Plugin                   m_plugin;

    bool is_current(optional<entry> const& e) const {
        return e->m_timestamp == m_timestamp;
    }

    optional<entry> const & get_core(Key const & k) const {
        unsigned id = m_plugin.to_int(k);
        if (id < m_map.size()) {
            optional<entry> const & e = m_map[id];
            if (e && is_current(e)) {
                return e;
            }
        }
        return optional<entry>::undef();
    }

    void really_flush() {
        typename vector<optional<entry> >::iterator it  = m_map.begin();
        typename vector<optional<entry> >::iterator end = m_map.end();
        for (; it != end; ++it) {
            optional<entry> & e = *it;
            if (e) {
                m_plugin.del_eh(e->m_key, e->m_data);
                e.set_invalid();
            }
        }
        m_garbage = 0;
        m_non_garbage = 0;
    }


public:

    array_map(Plugin const & p = Plugin()):m_timestamp(0), m_garbage(0), m_non_garbage(0), m_plugin(p) {}
    ~array_map() { really_flush(); }

    bool contains(Key const & k) const {
        return get_core(k);
    }

    Data const & get(Key const & k) const {
        optional<entry> const & e = get_core(k);
        SASSERT(e);
        return e->m_data;
    }

    void reset() { 
        if (m_timestamp < UINT_MAX) {
            m_timestamp++; 
        }
        else {
            really_flush();
            m_timestamp = 0;
        }
    }

    void insert(Key const & k, Data const & d) {
        unsigned id = m_plugin.to_int(k);
        if (id >= m_map.size()) {
            m_map.resize(id + 1, optional<entry>::undef());
        }
        
        m_plugin.ins_eh(k, d);
        optional<entry> & e = m_map[id];
        if (e) {
            if (!is_current(e)) {
                --m_garbage;
                ++m_non_garbage;
            }
            m_plugin.del_eh(e->m_key, e->m_data);
        }
        else {
            ++m_non_garbage;
        }
        e = entry(k, d, m_timestamp);
    }

    void erase(Key const & k) {
        unsigned id = m_plugin.to_int(k);
        if (id < m_map.size()) {
            optional<entry> & e = m_map[id];
            if (e) {
                m_plugin.del_eh(e->m_key, e->m_data);
                if (is_current(e)) {
                    SASSERT(m_non_garbage > 0);
                    --m_non_garbage;
                }
                else {
                    SASSERT(m_garbage > 0);
                    --m_garbage;
                }
                e.set_invalid();
            }
        }
    }
    
    void flush() {
        m_garbage += m_non_garbage;
        m_non_garbage = 0;
        if (m_garbage > m_gc_threshold) {
            really_flush();
        }
        else {
            reset();
        }
    }

    void finalize() {
        really_flush();
    }

};

#endif /* _ARRAY_MAP_H_ */
