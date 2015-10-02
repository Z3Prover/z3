/*++
Copyright (c) 2006 Microsoft Corporation

Module Name:

    var_offset_map.h

Abstract:

    A generic mapping from (var, offset) to a value T.

Author:

    Leonardo de Moura (leonardo) 2008-02-01.

Revision History:

--*/
#ifndef VAR_OFFSET_MAP_H_
#define VAR_OFFSET_MAP_H_

#include"ast.h"
#include"vector.h"

/**
   \brief A mapping from variable-id + offset to some value of type T.
*/
template<typename T>
class var_offset_map {
protected:
    struct data {
        T        m_data;
        unsigned m_timestamp;
        data():m_timestamp(0) {}
    };
    
    svector<data>           m_map;
    unsigned                m_num_offsets;
    unsigned                m_num_vars;
    unsigned                m_timestamp;

public:
    var_offset_map():
        m_num_offsets(0),
        m_num_vars(0),
        m_timestamp(1) {
    }

    void reset() {
        m_timestamp++;
        if (m_timestamp == UINT_MAX) {
            typename svector<data>::iterator it  = m_map.begin();
            typename svector<data>::iterator end = m_map.end();
            for (; it != end; ++it)
                it->m_timestamp = 0;
            m_timestamp = 1;
        }
    }

    unsigned offsets_capacity() const { return m_num_offsets; }

    unsigned vars_capacity() const { return m_num_vars; }

    void reserve(unsigned num_offsets, unsigned num_vars) {
        if (num_offsets > m_num_offsets || num_vars > m_num_vars) {
            unsigned sz = num_offsets * num_vars;
            m_map.resize(sz);
            m_num_vars    = num_vars;
            m_num_offsets = num_offsets;
        }
        reset();
    }

    void reserve_offsets(unsigned num_offsets) { reserve(num_offsets, m_num_vars); }

    void reserve_vars(unsigned num_vars) { reserve(m_num_offsets, num_vars); }

    void insert(unsigned v_idx, unsigned offset, T const & t) {
        SASSERT(v_idx < m_num_vars);
        SASSERT(offset < m_num_offsets);
        unsigned idx  = v_idx + offset * m_num_vars;
        SASSERT(idx < m_map.size());
        data & d = m_map[idx];
        d.m_data      = t;
        d.m_timestamp = m_timestamp;
    }

    void insert(var * v, unsigned offset, T const & t) { insert(v->get_idx(), offset, t); }
    
    bool find(unsigned v_idx, unsigned offset, T & r) const {
        SASSERT(v_idx < m_num_vars);
        SASSERT(offset < m_num_offsets);
        unsigned idx  = v_idx + offset * m_num_vars;
        data const & d = m_map[idx];
        SASSERT(d.m_timestamp <= m_timestamp);
        if (d.m_timestamp == m_timestamp) {
            r = d.m_data;
            return true;
        }
        return false;
    }
    
    bool find(var * v, unsigned offset, T & r) const { return find(v->get_idx(), offset, r); }

    void erase(unsigned v_idx, unsigned offset) {
        SASSERT(v_idx < m_num_vars);
        SASSERT(offset < m_num_offsets);
        unsigned idx  = v_idx + offset * m_num_vars;
        m_map[idx].m_timestamp = 0;
    }

};

#endif /* VAR_OFFSET_MAP_H_ */
