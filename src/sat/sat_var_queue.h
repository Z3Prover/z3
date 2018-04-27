/*++
Copyright (c) 2011 Microsoft Corporation

Module Name:

    sat_var_queue.h

Abstract:

    SAT variable priority queue.

Author:

    Leonardo de Moura (leonardo) 2011-05-21.

Revision History:

--*/
#ifndef SAT_VAR_QUEUE_H_
#define SAT_VAR_QUEUE_H_

#include "util/heap.h"
#include "sat/sat_types.h"

namespace sat {
    
    class var_queue {
        struct lt {
            svector<unsigned> & m_activity;
            lt(svector<unsigned> & act):m_activity(act) {}
            bool operator()(bool_var v1, bool_var v2) const { return m_activity[v1] > m_activity[v2]; }
        };
        heap<lt>  m_queue;
    public:
        var_queue(svector<unsigned> & act):m_queue(128, lt(act)) {}
        
        void activity_increased_eh(bool_var v) {
            if (m_queue.contains(v))
                m_queue.decreased(v);
        }

        void activity_changed_eh(bool_var v, bool up) {
            if (m_queue.contains(v)) {
                if (up) 
                    m_queue.decreased(v);
                else 
                    m_queue.increased(v);
            }
        }

        void mk_var_eh(bool_var v) {
            m_queue.reserve(v+1);
            m_queue.insert(v);
        }

        void del_var_eh(bool_var v) {
            if (m_queue.contains(v))
                m_queue.erase(v);
        }

        void unassign_var_eh(bool_var v) {
            if (!m_queue.contains(v))
                m_queue.insert(v);
        }

        void reset() {
            m_queue.reset();
        }

        bool empty() const { return m_queue.empty(); }

        bool_var next_var() { SASSERT(!empty()); return m_queue.erase_min(); }

        bool_var min_var() { SASSERT(!empty()); return m_queue.min_value(); }

        bool more_active(bool_var v1, bool_var v2) const { return m_queue.less_than(v1, v2); }
    };
};

#endif
