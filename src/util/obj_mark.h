/*++
Copyright (c) 2006 Microsoft Corporation

Module Name:

    obj_mark.h

Abstract:

    A mapping from object to boolean (for objects that can be mapped to unsigned integers).

Author:

    Leonardo de Moura (leonardo) 2008-01-02.

Revision History:

--*/
#ifndef OBJ_MARK_H_
#define OBJ_MARK_H_

#include"bit_vector.h"

template<typename T>
struct default_t2uint {
    unsigned operator()(T const & obj) const { return obj.get_id(); }
};

template<typename T, typename BV = bit_vector, typename T2UInt = default_t2uint<T> >
class obj_mark {
    T2UInt     m_proc;
    BV         m_marks;
public:
    obj_mark(T2UInt const & p = T2UInt()):m_proc(p) {}
    bool is_marked(T const & obj) const {
        unsigned id = m_proc(obj);
        return id < m_marks.size() && m_marks.get(id);
    }
    bool is_marked(T * obj) const { return is_marked(*obj); }
    void mark(T const & obj, bool flag) {
        unsigned id = m_proc(obj);
        if (id >= m_marks.size()) {
            m_marks.resize(id+1, 0);
        }
        m_marks.set(id, flag);
    }
    void mark(T const * obj, bool flag) { mark(*obj, flag); }
    void mark(T const & obj) { mark(obj, true); }
    void mark(T const * obj) { mark(obj, true); }
    void reset() { m_marks.reset(); }
};

#endif /* OBJ_MARK_H_ */
