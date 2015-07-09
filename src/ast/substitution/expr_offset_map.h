/*++
Copyright (c) 2006 Microsoft Corporation

Module Name:

    expr_offset_map.h

Abstract:

    A generic mapping from (expression, offset) to a value T.

Author:

    Leonardo de Moura (leonardo) 2008-02-01.

Revision History:

--*/
#ifndef EXPR_OFFSET_MAP_H_
#define EXPR_OFFSET_MAP_H_

#include"expr_offset.h"
#include"vector.h"

/**
   \brief A mapping from expr_offset to some value of type T.
*/
template<typename T>
class expr_offset_map {
    struct data {
        T        m_data;
        unsigned m_timestamp;
        data():m_timestamp(0) {}
    };
    vector<svector<data> > m_map;
    unsigned               m_timestamp;
public:
    expr_offset_map():
        m_timestamp(1) {}
    
    bool contains(expr_offset const & n) const {
        unsigned off = n.get_offset();
        if (off < m_map.size()) {
            svector<data> const & v = m_map[off];
            unsigned id             = n.get_expr()->get_id();
            if (id < v.size()) 
                return v[id].m_timestamp == m_timestamp;
        }
        return false;
    }

    bool find(expr_offset const & n, T & r) const {
        unsigned off = n.get_offset();
        if (off < m_map.size()) {
            svector<data> const & v = m_map[off];
            unsigned id             = n.get_expr()->get_id();
            if (id < v.size() && v[id].m_timestamp == m_timestamp) {
                r = v[id].m_data;
                return true;
            }
        }
        return false;
    }

    void insert(expr_offset const & n, T const & r) {
        unsigned off = n.get_offset();
        if (off >= m_map.size())
            m_map.resize(off+1, svector<data>());
        svector<data> & v = m_map[off];
        unsigned id       = n.get_expr()->get_id();
        if (id >= v.size())
            v.resize(id+1);
        v[id].m_data      = r;
        v[id].m_timestamp = m_timestamp;
    }

    void reset() {
        m_timestamp++;
        if (m_timestamp == UINT_MAX) {
            typename vector<svector<data> >::iterator it  = m_map.begin();
            typename vector<svector<data> >::iterator end = m_map.end();
            for (; it != end; ++it) {
                svector<data> & v = *it;
                typename svector<data>::iterator it2  = v.begin();
                typename svector<data>::iterator end2 = v.end();
                for (; it2 != end2; ++it2)
                    it2->m_timestamp = 0;
            }
            m_timestamp = 1;
        }
    }
};

#endif /* EXPR_OFFSET_MAP_H_ */
