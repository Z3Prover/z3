/*++
Copyright (c) 2011 Microsoft Corporation

Module Name:

    pvar_queue.h

Abstract:

    polysat variable priority queue.

Author:

    Leonardo de Moura (leonardo) 2011-05-21.

Revision History:

--*/
#pragma once

#include "util/heap.h"


class pvar_queue {
    typedef unsigned var;

    class lt {
        unsigned_vector const& m_size;
        unsigned_vector const& m_activity;
    public:
        lt(unsigned_vector const& sz, unsigned_vector const& act): m_size(sz), m_activity(act) {}
        bool operator()(var v1, var v2) const {
            return m_size[v1] > m_size[v2]
                || (m_size[v1] == m_size[v2] && m_activity[v1] > m_activity[v2]);
        }
    };

    heap<lt> m_queue;
public:

    pvar_queue(unsigned_vector const& sz, unsigned_vector const& act): m_queue(128, lt(sz, act)) {}

    void activity_increased_eh(var v) {
        if (m_queue.contains(v))
            m_queue.decreased(v);
    }

    void activity_changed_eh(var v, bool up) {
        if (m_queue.contains(v)) {
            if (up)
                m_queue.decreased(v);
            else
                m_queue.increased(v);
        }
    }

    void mk_var_eh(var v) {
        m_queue.reserve(v+1);
        unassign_var_eh(v);
    }

    void del_var_eh(var v) {
        if (m_queue.contains(v))
            m_queue.erase(v);
    }

    void unassign_var_eh(var v) {
        if (!m_queue.contains(v))
            m_queue.insert(v);
    }

    void reset() {
        m_queue.reset();
    }

    bool empty() const { return m_queue.empty(); }

    var next_var() { SASSERT(!empty()); return m_queue.erase_min(); }

    var min_var() { SASSERT(!empty()); return m_queue.min_value(); }

    std::ostream& display(std::ostream& out) const {
        bool first = true;
        for (auto v : m_queue) {
            if (first) {
                first = false;
            } else {
                out << " ";
            }
            out << v;
        }
        return out;
    }

    using const_iterator = decltype(m_queue)::const_iterator;
    const_iterator begin() const { return m_queue.begin(); }
    const_iterator end() const { return m_queue.end(); }
};

inline std::ostream& operator<<(std::ostream& out, pvar_queue const& queue) {
    return queue.display(out);
}
